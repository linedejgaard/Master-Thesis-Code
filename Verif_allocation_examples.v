Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.

Require Import VC.clientsfun.

Local Open Scope logic.


Definition kalloc_write_42_spec : ident * funspec :=
    DECLARE _kalloc_write_42
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) 
        SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec orig_head nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx orig_head * emp)
            else
            EX next ls',
                (!! (next :: ls' = ls /\
                    r = Vint (Int.repr 42)
                 ) &&
                    data_at sh tint (Vint (Int.repr 42)) orig_head *
                    memory_block sh (PGSIZE - sizeof tint)
                        (offset_val (sizeof tint) orig_head) *
                    KAF_globals gv  sh ls' xx next
            )
            )
        ).

Definition kalloc_int_array_spec : ident * funspec :=
    DECLARE _kalloc_int_array
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals, n:Z
    PRE [ tint ] 
    PROP (0 < n /\ 0 < sizeof (tarray tint n) /\ sizeof (tarray tint n) <= PGSIZE) (* make sure an array of size n fits into the page *)
    PARAMS(Vint (Int.repr n)) GLOBALS(gv) 
    SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tptr tint ]
    EX r,
    PROP ( r = orig_head ) RETURN ( r ) SEP (
        (if eq_dec orig_head nullval then
            KAF_globals gv  sh ls xx orig_head * emp
        else
        EX next ls',
            (!! (next :: ls' = ls) &&
                array_42_rep sh n orig_head *
                memory_block sh (PGSIZE - sizeof (tarray tint n))
                        (offset_val (sizeof (tarray tint n)) orig_head) *
                KAF_globals gv  sh ls' xx next
        )
        )
    ).

Definition kalloc_write_pipe_spec : ident * funspec :=
    DECLARE _kalloc_write_pipe
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tvoid ]
        PROP ( ) RETURN () SEP (
            (if eq_dec orig_head nullval then
                KAF_globals gv  sh ls xx orig_head *emp
            else
            EX next ls',
                (!! (next :: ls' = ls) &&
                    pipe_rep sh orig_head *
                    memory_block sh (PGSIZE - sizeof (t_struct_pipe))
                    (offset_val (sizeof (t_struct_pipe)) orig_head) *
                    KAF_globals gv  sh ls' xx next
            )
            )
        ).
       

Definition kalloc_int_array_spec_fail : ident * funspec :=
    DECLARE _kalloc_int_array
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals, n:Z
    PRE [ tint ] 
    PROP () (* make sure an array of size n fits into the page *)
    PARAMS(Vint (Int.repr n)) GLOBALS(gv) 
    SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tptr tint ]
    EX r,
    PROP ( r = orig_head ) RETURN ( r ) SEP (
        (if eq_dec orig_head nullval then
            KAF_globals gv  sh ls xx orig_head * emp
        else
        EX next ls',
            (!! (next :: ls' = ls) &&
                array_42_rep sh n orig_head *
                memory_block sh (PGSIZE - sizeof (tarray tint n))
                        (offset_val (sizeof (tarray tint n)) orig_head) *
                KAF_globals gv  sh ls' xx next
        )
        )
    ).

Lemma body_kalloc_write_42: semax_body KAFVprog KAFGprog f_kalloc_write_42 kalloc_write_42_spec.
Proof.
start_function.
Intros.
forward.
forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, orig_head). (* kalloc *)
+ (* The pre-conditions are met *) unfold KAF_globals. entailer!.
+ (* The proof continues *) if_tac_auto_contradict.
    * forward_if.
        -- rewrite H in H0; auto_contradict.
        -- forward. Exists (Vint(Int.repr 0)). entailer.
    * Intros ab.
    destruct ls; auto_contradict.
      forward_if.
        -- unfold type_kalloc_token. rewrite kalloc_token_sz_unfold.
        destruct orig_head eqn:eo; inversion H0; auto_contradict.
        assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus).
        { entailer. }
        rewrite token_merge with (b:= b) (i:= i); auto; try rep_lia.
        Intros.
        rewrite <- token_merge_size with (b:= b) (i:= i) (sz:=sizeof tint); auto; try rep_lia.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
        repeat forward.
        Exists (Vint(Int.repr 42)) (fst ab) (snd ab). entailer.
        -- forward.
Qed.

Lemma body_kalloc_int_array: semax_body KAFVprog KAFGprog f_kalloc_int_array kalloc_int_array_spec.
Proof.
start_function.
Intros.
forward. 
- forward_call (kalloc_spec_sub KAF_APD (tarray tint n)) (gv, sh , ls, xx, orig_head ). (* kalloc *)
    + unfold KAF_globals. entailer!.
    + if_tac_auto_contradict. 
        * forward_if.
        -- rewrite H0 in H1; auto_contradict.
        -- forward. Exists nullval. unfold KAF_globals. entailer!.
        * forward_if; auto_contradict.    
    Intros ab.
      destruct ls; auto_contradict.
        unfold type_kalloc_token. rewrite kalloc_token_sz_unfold. Intros.
        forward_for_simple_bound n
        (EX i:Z,
            PROP  ()
            LOCAL (
                temp _pa orig_head; gvars gv;
                temp _n (Vint (Int.repr n))
                ) 
            SEP (
                (
                    tmp_array_42_rep sh n orig_head i *
                    memory_block sh (PGSIZE - sizeof (tarray tint n))
                            (offset_val (sizeof (tarray tint n)) orig_head) *
                    KAF_globals gv sh ls xx v
                )
                )
            )%assert; destruct H as [HH1 HH2]; destruct HH2 as [HH2 HH3].
        ++ unfold tarray in HH3. rewrite sizeof_Tarray in HH3.
        assert (Z.max 0 n <= PGSIZE / (sizeof tint)). {  apply Zdiv_le_lower_bound. simpl; try rep_lia. auto. rewrite Z.mul_comm. auto. }
        assert (n <= PGSIZE / (sizeof tint)); try rep_lia. apply (Z.le_trans) with (PGSIZE / sizeof tint); try rep_lia.
        simpl; try rep_lia.
        ++ unfold tmp_array_42_rep, KAF_globals. inversion H2; entailer. (* ensure the pre-conditions for the loop is met *)
        destruct orig_head; auto_contradict.
        assert (Zrepeat (default_val tint) n = default_val (tarray tint n)) as Hdefault by (apply Zrepeat_default_val_array). 
        rewrite token_merge with (b:=b) (i:=i); auto; try rep_lia.
        rewrite <- Hdefault at 1.
        rewrite <- token_merge_size with (b:=b) (i:=i) (sz:=sizeof (tarray tint n)); auto; try rep_lia.
        rewrite memory_block_data_at_, data_at__eq; auto.
        entailer.
        ++ Intros. (* the postcondition of the loop body implies the loop invariant *)
        assert (Int.min_signed <= i <= Int.max_signed). { 
            assert (n <= Int.max_signed). {
            unfold tarray in HH3; rewrite sizeof_Tarray in HH3. 
            assert (Z.max 0 n <= PGSIZE / (sizeof tint)). {  apply Zdiv_le_lower_bound. simpl; try rep_lia. auto. rewrite Z.mul_comm. auto. }
            assert (n <= PGSIZE / (sizeof tint)); try rep_lia. apply (Z.le_trans) with (PGSIZE / sizeof tint). try rep_lia.
            unfold PGSIZE; simpl; try rep_lia.
            }
            split; try rep_lia.
        } unfold tmp_array_42_rep.
        forward. unfold tmp_array_42_rep. entailer!. 
        (* Rewrite the first array to match the form of the second (they are identical),
                enabling the entailer to resolve the rest. *)
        rewrite upd_Znth_unfold.
        ** rewrite sublist_firstn. 
        rewrite firstn_app1.
        assert (Zlength (array_42 (Z.to_nat i)) = i) as HH21. { rewrite array_42_length. try rep_lia. }
        rewrite Zlength_length in HH21; try rep_lia.
        rewrite <- HH21 at 1.
        rewrite firstn_exact_length with (xs :=array_42 (Z.to_nat i)); try rep_lia.
        rewrite sublist_app2.
        rewrite array_42_length.
        replace (i + 1 - Z.of_nat (Z.to_nat i)) with (1); try rep_lia.
        rewrite Zlength_app.
        rewrite array_42_length.
        replace (Z.of_nat (Z.to_nat i) + Zlength (Zrepeat (default_val tint) (n - i)) -
        Z.of_nat (Z.to_nat i)) with (Zlength (Zrepeat (default_val tint) (n - i))); try rep_lia.
        rewrite Zlength_Zrepeat; try rep_lia.
        rewrite sublist_Zrepeat; try rep_lia.
        replace (Z.to_nat (i + 1)) with (Z.to_nat (i) + 1)%nat; try rep_lia.
        rewrite <- array_42_append.
        replace (n - i - 1) with (n - (i + 1)); try rep_lia. 
        rewrite app_assoc. entailer!.
        --- rewrite array_42_length. try rep_lia.
        --- assert (Datatypes.length (array_42 (Z.to_nat i))%nat = Z.to_nat i) as HH21. {
            rewrite <- Zlength_length; try rep_lia.
            rewrite array_42_length.
            try rep_lia.
        }
        rewrite HH21; auto.
        ** rewrite Zlength_app. rewrite array_42_length. rewrite Zlength_Zrepeat; try rep_lia.
        ++ forward. (* the loop invariant (and negation of the loop condition) is a strong enough precondition to proceed and complete the proof after the loop. *)
        Exists orig_head v ls. entailer. unfold tmp_array_42_rep, array_42_rep. 
        replace (n - n) with 0; try rep_lia. 
        rewrite Zrepeat_0, app_nil_r. entailer.
Qed.

Lemma body_kalloc_int_array_fail: semax_body KAFVprog KAFGprog f_kalloc_int_array kalloc_int_array_spec_fail.
Proof.
start_function. Intros.
forward.
forward_call (kalloc_spec_sub KAF_APD (tarray tint n)) (gv, sh , ls, xx, orig_head ). (* kalloc *)
- unfold KAF_globals. entailer!.
- assert (exists n : Z, sizeof (tarray tint n) > PGSIZE). 
    {
        exists PGSIZE.
        split.
    }
    admit. (* this is not provable as n can be arbitrary large *)
Abort.

Lemma body_kalloc_write_pipe: semax_body KAFVprog KAFGprog f_kalloc_write_pipe kalloc_write_pipe_spec.
Proof.
start_function.
Intros.
forward.
forward_call (kalloc_spec_sub KAF_APD t_struct_pipe) (gv, sh , ls, xx, orig_head ). (* kalloc *)
- unfold KAF_globals. entailer!. 
- if_tac. 
    + forward_if.
        * rewrite H in H0; auto_contradict.
        * forward. entailer.
    + Intros ab. forward_if.
        * rewrite mem_mgr_unfold, type_kalloc_token_split, kalloc_token_sz_unfold.
        destruct orig_head; auto_contradict.
        assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus) as HH11. { Intros. entailer!. }
        rewrite token_merge with (b:= b) (i:= i); auto.
        2: { try rep_lia. }
        Intros.
        rewrite <- token_merge_size with (b:= b) (i:= i) (sz:=sizeof t_struct_pipe); auto; try rep_lia.
        3: { simpl; unfold PGSIZE; try rep_lia. }
        2: { simpl; try rep_lia. } 
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
        repeat forward. 
        Exists  (fst ab) (snd ab). entailer.
        unfold KAF_globals. unfold pipe_rep. Exists (fst (default_val t_struct_pipe)). entailer!.
        rewrite mem_mgr_unfold.
        entailer!.
        * forward.
        entailer.
Qed.
