(* ================================================================= *)
(** ** Functional model and lemmas for clients *)

Require Import VST.floyd.proofauto.
Require Import VC.tactics.
Require Import VC.kalloc.
Require Import VC.ASI_kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

Local Open Scope logic.

(* ================================================================= *)
(** ** Everything required for loops *)

(** ** Kalloc_tokens  *)

Fixpoint kalloc_tokens K (sh: share) (n: nat) (p: val) (size: Z) (t:type): mpred :=
  match n with
  | S n' => 
      kalloc_token' K sh (sizeof t) p  *
      kalloc_tokens K sh n' (offset_val size p) size (t) (* Move to the next slot *)
  | O => !! (p = nullval) && emp
  end.

Lemma kalloc_tokens_local_prop: forall K sh n p size t, 
  kalloc_tokens K sh n p size t |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros K sh n.
  induction n as [| n' IH].
  - unfold kalloc_tokens. entailer!. split; split; intros; auto; auto_contradict; try rep_lia.
  - unfold kalloc_tokens; fold kalloc_tokens. intros. sep_apply IH. entailer!. destruct p; auto_contradict.
  split; split; intros; try rep_lia; auto; auto_contradict.
  + split; intros; auto_contradict.
  + split; intros; auto; rep_lia.
Qed.
#[export] Hint Resolve kalloc_tokens_local_prop : saturate_local.

(** ** Add and sub offset lemmas  *)

Lemma add_add_offset_n:
   forall p size n,
   0 < size ->
   (0 < n) ->
   isptr p ->
   offset_val size (offset_val (n * size) p) = offset_val ((n + 1) * size) p.
Proof.
intros; destruct p; auto_contradict.
  - unfold offset_val.
  simpl. f_equal.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite<- ptrofs_mul_repr.
  rewrite<- ptrofs_mul_repr.
  rewrite <- ptrofs_add_repr.
  rewrite Ptrofs.mul_add_distr_l.
  replace (Ptrofs.repr 1) with (Ptrofs.one); auto.
  replace (Ptrofs.mul Ptrofs.one (Ptrofs.repr size)) with (Ptrofs.repr size). 
  2: {
  rewrite Ptrofs.mul_commut.
  rewrite Ptrofs.mul_one with (x:=Ptrofs.repr size). auto.
  }
  auto.
Qed.

Lemma sub_add_offset_n:
   forall p size n,
   0 < size ->
   (0 < n) ->
   isptr p ->
   offset_val (-size) (offset_val (n*size) p) = offset_val ((n-1)*size) p.
Proof.
intros; destruct p; auto_contradict.
  - unfold offset_val.
  simpl. f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite <- Ptrofs.neg_repr.
  f_equal.
  rewrite<- ptrofs_mul_repr.
  rewrite<- ptrofs_mul_repr.
  rewrite <- ptrofs_sub_repr.
  rewrite Ptrofs.sub_add_opp.
  rewrite Ptrofs.mul_add_distr_l.
  assert (Ptrofs.mul (Ptrofs.neg (Ptrofs.repr 1)) (Ptrofs.repr size) = Ptrofs.neg (Ptrofs.repr size)). {
    rewrite <- Ptrofs.neg_mul_distr_l.
    replace (Ptrofs.repr 1) with Ptrofs.one; auto.
    rewrite Ptrofs.mul_commut.
    rewrite Ptrofs.mul_one; auto.
  } rewrite H2. auto.
Qed.

(** ** Pointers list  *)

Fixpoint memory_pages_from (n: nat) (p: val) (size: Z) : list val :=
  match n with
  | O => []
  | S n' => p :: memory_pages_from n' (offset_val size p) size
  end.

Definition reversed_memory_pages_from n p size := rev (memory_pages_from n p size).

Lemma append_last_to_reversed_pages:
  forall n size q,
  reversed_memory_pages_from (S n) q size = reversed_memory_pages_from n (offset_val size q) size ++ [q].
Proof.
  intros.
  unfold reversed_memory_pages_from, memory_pages_from. fold memory_pages_from. 
  destruct n.
  - simpl. reflexivity.
  - simpl. auto.
Qed.

Lemma memory_pages_from_unroll_last : 
  forall n p size, 
    isptr p -> 
    memory_pages_from n p size ++ [offset_val (Z.of_nat n * size) p] = 
    memory_pages_from (S n) p size.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. intros p size H. rewrite Z.mul_0_l. unfold offset_val; destruct p; auto_contradict.
    rewrite Ptrofs.add_zero.
    reflexivity.
  - unfold memory_pages_from. fold memory_pages_from. intros.
    assert (offset_val (Z.of_nat (S n') * size) p = offset_val (Z.of_nat (n') * size) (offset_val size p)). {
      rewrite offset_offset_val.
      assert (size + Z.of_nat n' * size = (Z.of_nat (S n') * size)%Z). { try rep_lia. }
      rewrite H0. auto.
    }
  rewrite H0. 
  assert ( (memory_pages_from n' (offset_val size p) size) ++
        [offset_val (Z.of_nat n' * size) (offset_val size p)] = 
        memory_pages_from (S n') (offset_val size p) size
        ). { apply IHn'. auto. }
  rewrite <- app_comm_cons. rewrite H1.
  unfold memory_pages_from. fold memory_pages_from. auto.
Qed.

Lemma reversed_memory_pages_from_cons_last:
 forall n p size,
  isptr p ->
   (offset_val (Z.of_nat n * size)%Z p) :: reversed_memory_pages_from (n) p size =
   reversed_memory_pages_from n (offset_val size p) size ++ [p].
Proof.
  intros.
  rewrite <- append_last_to_reversed_pages.
  unfold reversed_memory_pages_from, memory_pages_from. fold memory_pages_from.
  rewrite <- rev_unit.
  f_equal.
  induction n.
  - simpl; auto. rewrite Z.mul_0_l. unfold offset_val; destruct p; auto_contradict. rewrite Ptrofs.add_zero; auto.
  - unfold memory_pages_from; fold memory_pages_from. rewrite <- app_comm_cons. f_equal. 
  assert (offset_val (Z.of_nat (S n) * size) p = offset_val (Z.of_nat (n) * size) (offset_val size p)). {
    rewrite offset_offset_val.
    assert (size + Z.of_nat n * size = (Z.of_nat (S n) * size)%Z). { try rep_lia. }
    rewrite H0. auto.
  }
  rewrite H0.
  rewrite memory_pages_from_unroll_last; auto.
Qed.

Definition pages_with_head (n: nat) (p: val) (size: Z) (head:val): list val :=
   match n with
   | O => nil
   | S O => [head]
   | S n' => reversed_memory_pages_from n' p size ++ [head]
   end.
Lemma pointers_with_head_empty :
   forall p size head,
   nil = pages_with_head 0 p size head.
Proof.
   intros. unfold pages_with_head; auto.
Qed.

Lemma add_to_pages_with_head:
 forall n p size hd,
  isptr p ->
  (0 < n)%nat ->
   (offset_val (Z.of_nat (n-1) * size)%Z p) :: pages_with_head (n) p size hd =
   pages_with_head (n+1) p size hd.
Proof.
  intros.
  induction (n+1)%nat eqn:e; try rep_lia.
  assert (n = n0); try rep_lia. rewrite H1.
  destruct n0; try rep_lia. 
  unfold pages_with_head.
  replace ((S n0) - 1)%nat  with (n0); try rep_lia.
  destruct n0; try rep_lia.
  - simpl. rewrite isptr_offset_val_zero; auto.
  - assert (offset_val (Z.of_nat (S n0) * size) p :: reversed_memory_pages_from (S n0) p size = reversed_memory_pages_from (S (S n0)) p size). {
    rewrite reversed_memory_pages_from_cons_last; auto.
  }
  rewrite <- H2.
  auto.
Qed.

(* ================================================================= *)
(** ** Other *)

(** ** pipes  *)

Definition t_struct_pipe := Tstruct _pipe noattr.

Definition pipe_rep sh (pi: val) : mpred :=
  EX data,
  data_at sh t_struct_pipe
    (
      (data), (* array data[PIPESIZE] *)
      (Vint (Int.repr 0), (* nread *)
      (Vint (Int.repr 0), (* nwrite *)
      (Vint (Int.repr 1), (* readopen *)
       Vint (Int.repr 1)  (* writeopen *))))
    ) pi.

(** ** 42 array  *)

Fixpoint array_42 (n : nat) : list val :=
  match n with
  | O => nil  (* If we have reached i == n, just return pa unchanged *)
  | S n' => (Vint (Int.repr 42)) :: array_42 n'  (* Recursively fill the array *)
  end.

Definition array_42_rep sh (n:Z) (pi: val) : mpred :=
  data_at sh (tarray (tint) n)
    (
      (array_42 (Z.to_nat n))
    ) pi.

Definition tmp_array_42_rep sh (n:Z) (pi: val) (i : Z) : mpred :=
  data_at sh (tarray (tint) n)
    (
      (array_42 (Z.to_nat i)) ++ (Zrepeat (default_val tint) (n - i))
    ) pi.
    
Lemma array_42_length :
    forall n,
    Zlength (array_42 n) = Z.of_nat n.
Proof.
    intros. induction n.
    - unfold array_42. rewrite calc_Zlength_nil. try rep_lia.
    - unfold array_42; fold array_42.
    rewrite Zlength_cons. rewrite IHn. try rep_lia.
Qed.

Lemma array_42_append :
    forall i,
    array_42 (i) ++ [Vint (Int.repr 42)] =  array_42 (i + 1).
Proof.
    intros. induction i.
    - simpl. auto. (*assert (i = 0); try rep_lia. rewrite H0. simpl. auto.*)
    - unfold array_42; fold array_42. simpl.
    f_equal. rewrite IHi. auto.
Qed. 

Lemma Zrepeat_default_val_array :
  forall (n:Z),
  Zrepeat (default_val tint) (n) = default_val (tarray tint (n)).
Proof.
intros n.
unfold default_val. simpl. auto.
Qed.
    