(** Kalloc Specification

    This specification is type-based.

    It utilizes the KallocTokenAPD from ASI_kalloc in 
    type_kalloc_token.
*)


Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.kallocfun.
Require Import VC.kalloc.


Global Open Scope funspec_scope.


(* ================================================================= *)
(** ** Type-based kalloc tokens *)

Definition type_kalloc_token K {cs: compspecs} sh t p :=
  !! field_compatible t [] p && (* this should work because of memory_block_data_at_*)
  (kalloc_token' K sh (sizeof t) p).

Lemma type_kalloc_token_valid_pointer:
  forall K (sh : share) (t : type) (p : val),
  type_kalloc_token K sh t p |-- valid_pointer p.
Proof.
  intros. 
  unfold type_kalloc_token. entailer!.
Qed.


(**
  Automates the proof by trying to prove a goal of the form:
      |- <kalloc_token> |-- valid_pointer p
*)

Ltac kalloc_token_data_at_valid_pointer :=
  match goal with |- ?A |-- valid_pointer ?p =>
   match A with
   | context [type_kalloc_token _ _ ?t p] =>
         try (assert (sizeof t <= 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         try (assert (sizeof t > 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         destruct (zlt 0 (sizeof t));
         auto with valid_pointer
   | context [kalloc_token_sz _ _ ?n p] =>
         try (assert (n <= 0) by rep_lia; fail 1);
         try (assert (n > 0) by rep_lia; fail 1);
         destruct (zlt 0 n);
         auto with valid_pointer
   end
 end.

(** Tell coq to apply the Ltac automatically *)
#[export] Hint Extern 1 (type_kalloc_token _ _ _ _ |-- valid_pointer _) =>
  (simple apply type_kalloc_token_valid_pointer; data_at_valid_aux) : valid_pointer.
#[export] Hint Extern 4 (_ |-- valid_pointer _) => kalloc_token_data_at_valid_pointer : valid_pointer.

Lemma type_kalloc_token_local_facts: forall K {cs: compspecs} sh t p,
      type_kalloc_token K sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold type_kalloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply kalloc_token'_local_facts.
Qed.
#[export] Hint Resolve type_kalloc_token_local_facts : saturate_local.


Lemma type_kalloc_token_split: 
 forall K (sh: share) (t: type) (p: val),
 type_kalloc_token K (sh) (t) (p)
  = 
  !! field_compatible t [] p &&
  (kalloc_token' K sh (sizeof t) p).
Proof.
  intros. apply pred_ext.
  - unfold type_kalloc_token. entailer.
  - unfold type_kalloc_token. entailer!.
Qed.


(* ================================================================= *)
(** ** Type-based specification of kalloc and kfree *)

Definition kfree_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) := 
  DECLARE _kfree
      WITH new_head:val, gv:globals, sh:share, ls: list val, xx:Z, orig_head:val
      PRE [ tptr tvoid]
        PROP(
              is_pointer_or_null new_head
              ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
          ASI_kalloc.mem_mgr K gv sh ls xx orig_head *
          (if eq_dec new_head nullval then emp
          else (type_kalloc_token K sh t new_head)
          )
        )
      POST [ tvoid ]
        PROP()
        RETURN () 
        SEP (
          if eq_dec new_head nullval then 
          ASI_kalloc.mem_mgr K gv sh ls xx orig_head
          else 
          (
            ASI_kalloc.mem_mgr K gv sh (orig_head::ls) xx new_head
          )).

Definition kalloc_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) :=
DECLARE _kalloc
WITH gv:globals, sh:share, ls: list val, xx:Z, orig_head:val
PRE [ ]
    PROP(0 < (sizeof t) <= PGSIZE;
            complete_legal_cosu_type t = true;
            natural_aligned natural_alignment t = true) 
    PARAMS () GLOBALS(gv)
    SEP ( ASI_kalloc.mem_mgr K gv sh ls xx orig_head)
POST [ tptr tvoid ]
    PROP()
    RETURN (orig_head) 
    SEP (
      if (eq_dec orig_head nullval) then
        (ASI_kalloc.mem_mgr K gv sh ls xx orig_head * emp)
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              type_kalloc_token K sh t orig_head * 
              ASI_kalloc.mem_mgr K gv sh ls' xx next
        )
        )
    ).


(* ================================================================= *)
(** ** How to use the type-based specification of kalloc and kfree *)

Lemma kalloc_spec_sub:
  forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), 
    funspec_sub (snd (kalloc_spec' K _kalloc)) (snd (kalloc_spec K t)).
  Proof.
    do_funspec_sub. 
    entailer.
    destruct w.
    repeat (destruct p).
    Exists (sizeof t, g0, s, l, z, v) emp. entailer.
    if_tac.
    - entailer!. entailer!.
    - entailer!.
      + entailer!. Exists next ls'. entailer!. unfold type_kalloc_token. 
      assert_PROP (field_compatible t [] (eval_id ret_temp x)).
      { entailer!.
        apply malloc_compatible_field_compatible; auto. }
      entailer.
Qed.

Lemma kfree_spec_sub:
forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), 
  funspec_sub (snd (kfree_spec' K _kfree)) (snd (kfree_spec K t)).
Proof.
  do_funspec_sub. 
  destruct w.
  repeat (destruct p).
  Exists (sizeof t, v0, g0, s, l, z, v) emp.
  entailer!.
  destruct (EqDec_val v0 nullval) eqn:Heq; entailer.
  unfold type_kalloc_token. entailer.
Qed.


(* ================================================================= *)
(** ** Ltac *)

(** ** 
  Example usage (assuming kalloc_token' = kalloc_token_sz): 
    kalloc_token' KAF_APD sh (sizeof t_run) new_head
    |-- type_kalloc_token KAF_APD sh t_run new_head

*)

Ltac simplify_kalloc_token :=
  repeat (
    rewrite kalloc_token_sz_unfold;
    unfold type_kalloc_token
  );
  entailer!.
