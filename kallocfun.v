Require Import VST.floyd.proofauto.

Require Import VC.tactics.
Require Import VC.kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

(* ================================================================= *)
(** ** Types and defs *)

Definition PGSIZE : Z := 4096.
Definition t_run := Tstruct _run noattr.
Definition t_struct_kmem := Tstruct _struct_kmem noattr.

Definition t_run_size := sizeof t_run.

(* ================================================================= *)
(** ** Size-based kalloc tokens *)

Definition pointer_malloc_compatible p : Prop :=
  (forall n : Z, ((isptr p /\ malloc_compatible (n) p))).

Definition kalloc_token_sz (sh: share) (n: Z) (p: val) : mpred :=
  !! (
      0 < n <= PGSIZE 
      /\ pointer_malloc_compatible p
      /\ writable_share sh
      /\ field_compatible t_run [] p (* ensure p is compatible with the layout of t_run *)
      /\ malloc_compatible (sizeof t_run) p 
      /\ 0 < (sizeof t_run) <= PGSIZE 
  ) && (
  (sepcon (memory_block sh (t_run_size) (p)) (memory_block sh (PGSIZE - t_run_size)
  (offset_val t_run_size p)))).

Lemma kalloc_token_sz_valid_pointer:
  forall (sh : share) (sz : Z) (p : val),
  kalloc_token_sz sh sz p |-- valid_pointer p.
Proof.
  intros. 
  unfold kalloc_token_sz. unfold t_run_size. entailer.
Qed.

Lemma  kalloc_token_sz_local_facts : 
 forall (sh : share) (n:Z) (p : val) ,
   kalloc_token_sz sh n p |-- !! malloc_compatible n p.
Proof.
  intros. 
  unfold kalloc_token_sz. Intros. entailer. unfold pointer_malloc_compatible in H0.
  specialize (H0 n). entailer!.
  destruct H0 as [HH0 HH3].
  auto. 
Qed.

Ltac safe_to_store_PGSIZE H p :=
  unfold pointer_malloc_compatible in H;
  specialize (H PGSIZE);
  destruct H as [Hyp1 H];
  unfold malloc_compatible in H;
  destruct p; auto_contradict; destruct H; auto.

Lemma kalloc_token_sz_unfold:
forall  (sh: share) (n: Z) (p: val),
  kalloc_token_sz sh n p =
  !! (
      0 < n <= PGSIZE 
      /\ pointer_malloc_compatible p
      /\ writable_share sh
      /\ field_compatible t_run [] p (* make sure t_run fits*)
      /\ malloc_compatible (sizeof t_run) p 
      /\ 0 < (sizeof t_run) <= PGSIZE 
      /\ match p with
         | Vptr _ ofs => Ptrofs.unsigned ofs + PGSIZE < Ptrofs.modulus
         | _ => False
         end
      (*/\  maybe some alignment and physical address checks here *))
  && ((*sepcon (pointer_malloc_compatible p) *)
  (sepcon (memory_block sh (t_run_size) (p)) (memory_block sh (PGSIZE - t_run_size)
  (offset_val t_run_size p))) ).
Proof.
  intros. apply pred_ext.
  - unfold kalloc_token_sz. entailer. safe_to_store_PGSIZE H0 p. entailer!.
  - unfold kalloc_token_sz. entailer!.
Qed.

Lemma token_merge :
forall (sh: share) (p:val) b i,
isptr p ->
p = Vptr b i ->
PGSIZE + Ptrofs.unsigned i < Ptrofs.modulus ->
(sepcon (memory_block sh t_run_size p)
  (memory_block sh (PGSIZE - t_run_size) (offset_val t_run_size p)) 
  = memory_block sh PGSIZE p
  ).
Proof.
destruct p; auto_contradict.
assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH. { rewrite Ptrofs.repr_unsigned. auto. }
unfold offset_val. rewrite Ptrofs.add_unsigned.
rewrite Ptrofs.unsigned_repr.
intros.
rewrite HH at 1.
rewrite <- memory_block_split.
assert (t_run_size + (PGSIZE - t_run_size) = PGSIZE) as Hpgsz; try rep_lia.
rewrite Hpgsz. rewrite HH at 2. auto.
- unfold t_run_size. simpl; try rep_lia.
- unfold t_run_size. simpl; try rep_lia.
- unfold t_run_size. simpl; try rep_lia. split; try rep_lia.
inversion H0. unfold PGSIZE in H1; auto.
- unfold t_run_size. simpl; try rep_lia.
Qed.

Lemma token_merge_size :
forall (sh: share) (p:val) b i sz,
isptr p ->
p = Vptr b i ->
PGSIZE + Ptrofs.unsigned i < Ptrofs.modulus ->
0 <= sz <= Ptrofs.max_unsigned ->
0 <= sz <= PGSIZE ->
(sepcon (memory_block sh sz p)
  (memory_block sh (PGSIZE - sz) (offset_val sz p)) 
  = memory_block sh PGSIZE p
  ).
Proof.
destruct p; auto_contradict.
assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH. { rewrite Ptrofs.repr_unsigned. auto. }
unfold offset_val. intros. rewrite HH at 2. rewrite Ptrofs.add_unsigned.
rewrite Ptrofs.unsigned_repr; try rep_lia.
rewrite HH at 1.
rewrite Ptrofs.unsigned_repr; try rep_lia.
rewrite <- memory_block_split.
assert (sz + (PGSIZE - sz) = PGSIZE) as Hpgsz; try rep_lia.
rewrite Hpgsz. rewrite HH at 2. auto.
- unfold t_run_size. simpl; try rep_lia.
- rewrite <- Zle_minus_le_0; try rep_lia.
- assert (sz + (PGSIZE - sz) = PGSIZE) as Hpgsz; try rep_lia. rewrite Hpgsz.
inversion H0. split; try rep_lia.
Qed.


(* ================================================================= *)
(** ** Defining freelistrep *)

Fixpoint freelistrep (sh: share) (il: list val) (p: val) : mpred := 
  (* The list contains the next pointer in the freelist *)
  match il with
  | next::il' =>
      (!!(malloc_compatible (sizeof t_run) p 
         /\ pointer_malloc_compatible p
        ) 
      && (
        (* Ensure that at location p, there is a t_run structure with value next *)
        sepcon (sepcon (data_at sh t_run next p) 
                     (memory_block sh (PGSIZE - t_run_size) (offset_val t_run_size p)))  
        (* Recursive call to process the next pointer in the freelist, sepcon ensures no loops *)
        (freelistrep sh il' next)
      ))
  | nil => 
      (* Base case: if the list is empty, p should be nullval *)
      !! (p = nullval) && emp
  end.


Arguments freelistrep sh il p : simpl never.

Lemma freelistrep_local_prop: forall sh n p, 
   freelistrep sh n p |--  !! (is_pointer_or_null p /\ (n=nil<->p=nullval) /\ ((n <> nil)<->isptr p))%nat.
Proof.
  intros.
  induction n as [| n' IH].
  - unfold freelistrep. entailer!. split; auto.
    + split; auto.
    + split; try lia. intros. simpl in *. auto_contradict. intros; auto_contradict.
  - unfold freelistrep. fold freelistrep. destruct p; entailer!. split.
    + split; intros; inversion H4.
    + split; intros; auto. unfold not; intros. auto_contradict.
   Qed.
#[export] Hint Resolve freelistrep_local_prop : saturate_local.

Lemma freelistrep_valid_pointer:
  forall sh n p, 
  readable_share sh ->
   freelistrep sh n p |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold freelistrep. entailer!.
  - unfold freelistrep. entailer.
Qed. 
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.

Ltac refold_freelistrep :=
  unfold freelistrep;
  fold freelistrep.
