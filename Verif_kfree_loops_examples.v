Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.ASI_kalloc.
Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.

Require Import VC.clientsfun.

Local Open Scope logic.

Definition kfree_kfree_kalloc_loop_spec := 
    DECLARE _kfree_kfree_kalloc_loop
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1 /\ (* just assume it is a pointer for simplicity *)
            Int.min_signed <= Int.signed (Int.repr 2) + Int.signed (Int.repr 1) <= Int.max_signed
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (2)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (offset_val PGSIZE pa1) (* we return the head like in the pop function*)
            SEP 
            (
                kalloc_token' KAF_APD sh (sizeof t_run) (offset_val PGSIZE pa1) *
                KAF_globals gv sh (orig_head::ls) xx pa1
            ).

Definition kfree_loop_spec := 
    DECLARE _kfree_loop
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        )
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tvoid ]
        EX head, EX added_elem,
        PROP( 
            added_elem = (pages_with_head (Z.to_nat n) (pa1) PGSIZE orig_head) /\
            head = (hd nullval ((pages_with_head (Z.to_nat n+1) (pa1) PGSIZE orig_head)))
            )
            RETURN () 
            SEP 
            (
                KAF_globals gv sh (added_elem++ls) xx head
            ).

Definition kfree_loop_kalloc_spec := 
    DECLARE _kfree_loop_kalloc
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tptr tvoid ]
        EX head, EX elems, 
        PROP( 
            (* before alloc *)
            elems = (pages_with_head (Z.to_nat n) (pa1) PGSIZE orig_head) ++ ls /\
            head = (hd nullval ((pages_with_head (Z.to_nat n+1) (pa1) PGSIZE orig_head)))
            )
            RETURN (head) (* we return the head like in the kalloc function*)
            SEP 
            (
            if eq_dec head nullval then
                emp * KAF_globals gv sh elems xx head
            else
                (KAF_globals gv sh (tl elems) xx (hd nullval elems) *
                kalloc_token' KAF_APD sh (sizeof t_run) head)
            ).

Definition kfree_loop_kalloc_tint_spec := 
    DECLARE _kfree_loop_kalloc
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tptr tvoid ]
        EX head, EX elems, 
        PROP( 
            (* before alloc *)
            elems = (pages_with_head (Z.to_nat n) (pa1) PGSIZE orig_head) ++ ls /\
            head = (hd nullval ((pages_with_head (Z.to_nat n+1) (pa1) PGSIZE orig_head)))
            )
            RETURN (head) (* we return the head like in the kalloc function*)
            SEP 
            (
            if eq_dec head nullval then
                emp * KAF_globals gv sh elems xx head
            else
                (KAF_globals gv sh (tl elems) xx (hd nullval elems) *
                kalloc_token' KAF_APD sh (sizeof tint) head)
            ).

Definition kfree_loop_kalloc_tlong_spec := 
    DECLARE _kfree_loop_kalloc
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tptr tvoid ]
        EX head, EX elems, 
        PROP( 
            (* before alloc *)
            elems = (pages_with_head (Z.to_nat n) (pa1) PGSIZE orig_head) ++ ls /\
            head = (hd nullval ((pages_with_head (Z.to_nat n+1) (pa1) PGSIZE orig_head)))
            )
            RETURN (head) (* we return the head like in the kalloc function*)
            SEP 
            (
            if eq_dec head nullval then
                emp * KAF_globals gv sh elems xx head
            else
                (KAF_globals gv sh (tl elems) xx (hd nullval elems) *
                kalloc_token' KAF_APD sh (sizeof tlong) head)
            ).


Definition KAFGprog_clients: funspecs := KAFGprog ++ [kfree_loop_spec].


Lemma body_kfree_kfree_kalloc_loop: semax_body  KAFVprog KAFGprog f_kfree_kfree_kalloc_loop kfree_kfree_kalloc_loop_spec.
Proof.
    start_function.
    Intros. forward.
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= 2 /\
        ((curr_head = orig_head /\ i = 0) \/ (curr_head = (offset_val (-PGSIZE) (p_tmp))  /\ i <> 0)) /\
        tmp_added_elem = (pages_with_head (Z.to_nat i) (pa1) PGSIZE orig_head) /\
        p_tmp = offset_val (i * PGSIZE)%Z pa1 /\
        Int.min_signed <=
        Int.signed (Int.repr i) + Int.signed (Int.repr 1) <=
        Int.max_signed 
    )
    LOCAL (
        gvars gv;
        temp _pa_start p_tmp;
        temp _i (Vint (Int.repr i))
        ) 
    SEP (
        (
        KAF_globals gv sh (tmp_added_elem ++ ls) xx curr_head *
        kalloc_tokens Tok_APD sh (Z.to_nat(2-i)) p_tmp (PGSIZE) t_run
        )
        )
    )%assert; destruct H as [H H3].
    - entailer. Exists 0 pa1 orig_head (pages_with_head (Z.to_nat 0) pa1 PGSIZE orig_head). (*entailer. *)
        rewrite <- pointers_with_head_empty. simpl; entailer!; unfold offset_val in H2; destruct pa1; auto_contradict.
    - entailer.
    - Intros. destruct (Z.to_nat (2 - i)) eqn:e.
        +assert (i = 2); try rep_lia.
        + forward_call (kfree_spec_sub KAF_APD t_run) (p_tmp, gv, sh , (tmp_added_elem ++ ls), xx,curr_head). (* call kfree*)
            * if_tac; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
                -- unfold offset_val in H1. destruct pa1; auto_contradict.
                --unfold KAF_globals. unfold type_kalloc_token. rewrite kalloc_token_sz_unfold. simpl. rewrite kalloc_token_sz_unfold. Intros.
                simpl. 
                entailer!.
            * destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04. unfold is_pointer_or_null.
              unfold offset_val. destruct pa1; auto_contradict; auto.
            * forward. entailer!. destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04. unfold is_pointer_or_null.
            unfold offset_val. destruct pa1; auto_contradict; auto.
            forward. if_tac; auto_contradict; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
                -- unfold offset_val in H1. destruct pa1; auto_contradict.
                -- Exists ((((i+1)%Z, (offset_val PGSIZE p_tmp):val), p_tmp:val), (curr_head::(pages_with_head(Z.to_nat (i)) pa1 PGSIZE)orig_head):list val).
                entailer!. 
                ++ split; try rep_lia. split.
                    ** right. split; try rep_lia. replace (i * PGSIZE + PGSIZE + - PGSIZE) with (i * PGSIZE)%Z; try rep_lia.
                    auto.
                    ** split.
                        --- destruct H02 as [[H0211 H0212] | [H0221 H0222]].
                            +++ rewrite H0212. simpl. rewrite H0211. auto.
                            +++ rewrite sub_add_offset_n in H0221; auto; try rep_lia.
                            2: {
                            unfold PGSIZE; try rep_lia.
                            }
                            rewrite H0221.
                            replace (i - 1) with (Z.of_nat ((Z.to_nat i) - 1)%nat); try rep_lia.
                            replace (Z.to_nat (i + 1)) with (((Z.to_nat i) + 1)%nat); try rep_lia.
                            rewrite add_to_pages_with_head; auto; try rep_lia.
                        --- replace (i * PGSIZE + PGSIZE) with ((i + 1) * PGSIZE)%Z; try rep_lia; auto.
                ++ unfold KAF_globals. 
                assert (Z.to_nat (2 - (i + 1)) = n); try rep_lia.
                rewrite H6. rewrite app_comm_cons. entailer!.
    - forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , pa1::orig_head::ls, xx, offset_val PGSIZE pa1). (* kalloc *)
        +
        entailer. destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
        unfold KAF_globals. rewrite H03.
        rewrite mem_mgr_unfold.
         
        assert (i = 2); try rep_lia. rewrite H0. destruct (0 <? Z.to_nat 2)%nat eqn:ei; try rep_lia.
        * destruct H02 as [[H021 H022] | [H031 H032]]; try rep_lia.
          rewrite H04 in H031. rewrite sub_add_offset_n in H031; auto; try rep_lia.
          Intros.
          destruct (Z.to_nat 2) eqn:e2; auto_contradict.
          unfold pages_with_head.
          destruct n eqn:en; try rep_lia.
          destruct n0 eqn:en0; try rep_lia.
          simpl. rewrite mem_mgr_unfold. refold_freelistrep. entailer!. entailer!.
          unfold PGSIZE; rep_lia.
        * rewrite Nat.ltb_ge in ei. try rep_lia.
        + destruct H0 as [H01 [H02 [H03 [H04 H05]]]].
        forward. if_tac.
        assert (isptr (offset_val PGSIZE pa1)). {
            apply isptr_offset_val'; auto.
        }
        rewrite H1 in H2; auto_contradict.
        Intros ab. unfold type_kalloc_token, KAF_globals. 
        inversion H2. entailer!.
Qed.


Lemma body_kfree_loop: semax_body KAFVprog KAFGprog f_kfree_loop kfree_loop_spec.
Proof.
start_function.
Intros. forward.
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= n /\
        ((curr_head = orig_head /\ i = 0) \/ (curr_head = (offset_val (-PGSIZE) (p_tmp))  /\ i <> 0)) /\
        tmp_added_elem = (pages_with_head (Z.to_nat i) (pa1) PGSIZE orig_head) /\
        p_tmp = offset_val (i * PGSIZE)%Z pa1 /\
        Int.min_signed <=
        Int.signed (Int.repr i) + Int.signed (Int.repr 1) <=
        Int.max_signed 
    )
    LOCAL (
        gvars gv;
        temp _pa_start p_tmp;
        temp _i (Vint (Int.repr i));
        temp _n (Vint (Int.repr n))
        ) 
    SEP (
        (
            KAF_globals gv sh (tmp_added_elem ++ ls) xx curr_head *
            kalloc_tokens Tok_APD sh (Z.to_nat(n-i)) p_tmp (PGSIZE) t_run
        )
    ))%assert; destruct H as [H01 [H02 H03]].
- (* the precondition (of the whole loop) implies the loop invariant *)
    entailer. Exists 0 pa1 orig_head (pages_with_head (Z.to_nat 0) pa1 PGSIZE orig_head). 
    rewrite <- pointers_with_head_empty. entailer. destruct (Z.to_nat n).
        + rewrite <- H0 in H01. try rep_lia.
        + rewrite app_nil_l. entailer!.
- (* the loop-condition expression type-checks (i.e., guarantees to evaluate successfully); that is, i and n can be compared using "<" *)
    entailer.
- (* he postcondition of the loop body implies the loop invariant *) 
    Intros. destruct (Z.to_nat (n - i)) eqn:e1.
    + try rep_lia.
    + destruct H0 as [H001 [H002 [H003 [H04 H05]]]]. forward_call (kfree_spec_sub KAF_APD t_run) (p_tmp, gv, sh , (tmp_added_elem ++ ls), xx,curr_head). (* call kfree *)
        * (* pre-conditions for calling kfree is met (SEP) *) 
            if_tac.
            -- rewrite H04 in H. unfold offset_val in H. destruct pa1; auto_contradict.
            -- unfold KAF_globals. unfold type_kalloc_token. unfold kalloc_tokens; fold kalloc_tokens. simplify_kalloc_token.
        * (* pre-conditions for calling kfree is met (PROP) *)  
            rewrite H04.
            assert ( isptr (offset_val (i * PGSIZE) pa1)). { apply isptr_offset_val'. auto. }
            auto.
        * repeat forward.
            assert (isptr (p_tmp)). { rewrite H04. apply isptr_offset_val'. auto. }
            Exists ((((i+1)%Z, (offset_val PGSIZE p_tmp):val), p_tmp:val), ((pages_with_head(Z.to_nat (i+1)) pa1 PGSIZE)orig_head):list val).
            entailer!.
                -- do 2 split; try rep_lia.
                    ++ right. split. assert (i * PGSIZE + PGSIZE + - PGSIZE = (i * PGSIZE)%Z) as Hdelt0; try rep_lia. rewrite Hdelt0. auto. unfold not.
                    intros; try rep_lia.
                    ++ split.
                        ** assert ((i * PGSIZE + PGSIZE) = (i + 1) * PGSIZE)%Z as Heq; try rep_lia. rewrite Heq. auto.
                        ** split; try rep_lia.
                            assert (n + 1 <= Int.max_signed); try rep_lia.
                            rewrite Int.signed_repr in H02; try rep_lia. rewrite Int.signed_repr in H02; try rep_lia.
                -- if_tac.
                    ++ rewrite H4 in H. auto_contradict.
                    ++ unfold KAF_globals.
                    assert (Z.to_nat (n - (i + 1)) = n0) as HH0; try rep_lia.
                    rewrite HH0.
                    assert (curr_head :: pages_with_head (Z.to_nat (i)) pa1 PGSIZE orig_head = pages_with_head (Z.to_nat (i + 1)) pa1 PGSIZE orig_head) as HH5. {
                        destruct (Z.to_nat i) eqn:ei.
                        - simpl. assert (Z.to_nat (i + 1) = (1)%nat) as Hi0; try rep_lia. rewrite Hi0.
                        simpl. destruct H002 as [[H0021 H0022] | [H0021 H0022]]; try rep_lia.
                        rewrite H0021. auto.
                        - assert ((Z.to_nat (i + 1)) = (Z.to_nat (i) + 1)%nat) as HH5; try rep_lia.
                        rewrite HH5.
                        rewrite <- add_to_pages_with_head; auto; try rep_lia.
                        destruct H002 as [[H0021 H0022] | [H0021 H0022]]; try rep_lia.
                        rewrite H0021. rewrite sub_add_offset_n; try rep_lia; auto.
                        2: { unfold PGSIZE; rep_lia. }
                        rewrite ei at 2.
                        replace (Z.of_nat (Z.to_nat i - 1)) with (i - 1); try rep_lia. auto.
                    }
                    rewrite app_comm_cons.
                    rewrite HH5. entailer.
- (* the loop invariant (and negation of the loop condition) is a strong enough precondition to prove *)
    forward. Exists curr_head tmp_added_elem. 
    unfold KAF_globals. 
    destruct H0 as [H001 [[[H0021 H0022] | [H0021 H0022]] [H003 [H04 H05]]]]; destruct (Z.to_nat (n - i)) eqn:eni; try rep_lia.
    + replace n with 0; try rep_lia. unfold kalloc_tokens. entailer!.
    + assert (i = n); try rep_lia. unfold kalloc_tokens. rewrite H. entailer!.
    rewrite <- add_to_pages_with_head; auto; try rep_lia. 
    assert ((n * PGSIZE + - PGSIZE)%Z = (n-1) * PGSIZE)%Z; try rep_lia.
    rewrite H.
    simpl. assert ((Z.of_nat (Z.to_nat n - 1) * PGSIZE)%Z = ((n - 1) * PGSIZE)%Z). { unfold PGSIZE. try rep_lia. }
    rewrite H1. auto.
Qed.

Lemma body_kfree_loop_kalloc: semax_body KAFVprog KAFGprog_clients f_kfree_loop_kalloc kfree_loop_kalloc_spec.
Proof.
start_function. destruct H as [H1 [H2 H3]].
forward_call (sh, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z). (* kfree_loop *)
Intros vret. unfold KAF_globals.
forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , snd vret ++ ls, xx,  fst vret ). (* kalloc *)
forward. if_tac.
- Exists (fst vret) (snd vret ++ ls); if_tac_auto_contradict; entailer.
- Intros ab. Exists (fst vret) (snd vret ++ ls). if_tac_auto_contradict. unfold KAF_globals. entailer.
    simplify_kalloc_token. destruct (snd vret ++ ls) eqn:elssndvret; auto_contradict.
    simpl. inversion H6. entailer.
Qed.


Lemma body_kfree_loop_kalloc_tint: semax_body KAFVprog KAFGprog_clients f_kfree_loop_kalloc kfree_loop_kalloc_tint_spec.
Proof.
start_function. destruct H as [H1 [H2 H3]].
forward_call (sh, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z). (* kfree_loop *)
Intros vret. unfold KAF_globals.
forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , snd vret ++ ls, xx,  fst vret ). (* kalloc *)
forward. if_tac.
- Exists (fst vret) (snd vret ++ ls); if_tac_auto_contradict; entailer.
- Intros ab. Exists (fst vret) (snd vret ++ ls). if_tac_auto_contradict. unfold KAF_globals. entailer.
    simplify_kalloc_token. destruct (snd vret ++ ls) eqn:elssndvret; auto_contradict.
    simpl. inversion H6. entailer.
Qed.

Lemma body_kfree_loop_kalloc_tlong: semax_body KAFVprog KAFGprog_clients f_kfree_loop_kalloc kfree_loop_kalloc_tlong_spec.
Proof.
start_function. destruct H as [H1 [H2 H3]].
forward_call (sh, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z). (* kfree_loop *)
Intros vret. unfold KAF_globals.
forward_call (kalloc_spec_sub KAF_APD tlong) (gv, sh , snd vret ++ ls, xx,  fst vret ). (* kalloc *)
forward. if_tac.
- Exists (fst vret) (snd vret ++ ls); if_tac_auto_contradict; entailer.
- Intros ab. Exists (fst vret) (snd vret ++ ls). if_tac_auto_contradict. unfold KAF_globals. entailer.
    simplify_kalloc_token. destruct (snd vret ++ ls) eqn:elssndvret; auto_contradict.
    simpl. inversion H6. entailer.
Qed.