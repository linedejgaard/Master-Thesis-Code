Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.ASI_kalloc.
Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.

Require Import VC.clientsfun.

Local Open Scope logic.


Definition kfree_kalloc_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, orig_head:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(is_pointer_or_null new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec new_head nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) new_head))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP( 
            ((new_head = nullval) /\ ( orig_head = nullval) /\ r = nullval) \/
            ((new_head <> nullval) /\  r = new_head) \/
            ((new_head = nullval) /\ ( orig_head <> nullval) /\ r = orig_head)
        )
        RETURN (r) (* we return the head like in the pop function*)
        SEP (
            let freelist_case :=
            if eq_dec orig_head nullval then
            emp * KAF_globals gv sh ls xx orig_head
            else
            EX next, EX ls',
                !! (next :: ls' = ls) &&
                KAF_globals gv sh ls' xx next *
                kalloc_token' KAF_APD sh (sizeof t_run) orig_head
        in
        
        let newhead_case :=
            KAF_globals gv sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
        in
        
        if eq_dec new_head nullval then
            freelist_case
        else
            newhead_case
).


Definition kfree_kalloc_inverses_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, orig_head:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(isptr new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof tint) new_head
        )
    POST [ tptr tvoid ]
        PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            KAF_globals gv sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof tint) new_head
    ).

Definition kfree_kalloc_inverses_t_run_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, orig_head:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(isptr new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
        )
    POST [ tptr tvoid ]
        PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            KAF_globals gv sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
    ).

Definition kfree_kalloc_inverses_tlong_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, orig_head:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(isptr new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof tlong) new_head
        )
    POST [ tptr tvoid ]
        PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            KAF_globals gv sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof tlong) new_head
    ).
    


Definition kalloc_kfree_inverses_spec : ident * funspec :=
    DECLARE _kalloc_kfree
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tvoid ] 
        PROP ( ) RETURN () 
        SEP (
            KAF_globals gv sh ls xx orig_head
        ).

Definition kalloc_write_42_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_42_kfree
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec orig_head nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx orig_head)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                KAF_globals gv  sh ls xx orig_head)
            )
        ).
        
Definition kfree_kalloc_twice_spec:= 
    DECLARE _kfree_kalloc_twice
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head <> nullval) /\ (r = orig_head)) \/ (* then there is exists a value or null in ls that is returned *)
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head <> nullval)) (* r is either nullval or next next*)
            ) 
            RETURN (r) (* we return the head like in the pop function*)
            SEP 
            (
                let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                (if eq_dec orig_head nullval then
                    KAF_globals gv sh ls xx orig_head * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec orig_head nullval then 
                        KAF_globals gv sh ls xx orig_head * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KAF_globals gv sh ls' xx next *
                        kalloc_token' KAF_APD sh (sizeof t_run) orig_head) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec orig_head nullval then
                        emp * KAF_globals gv sh ls xx orig_head
                    else
                        (kalloc_token' KAF_APD sh (sizeof t_run) orig_head *
                        (EX next1, EX ls1,
                        !! (next1:: ls1 = ls) &&
                        if eq_dec next1 nullval then
                            KAF_globals gv sh ls1 xx next1
                        else (
                        EX next2, EX ls2,
                        !! (next2:: ls2 = ls1) &&
                        KAF_globals gv sh ls2 xx next2 * 
                        kalloc_token' KAF_APD sh (sizeof t_run) next1
                        )))
                in
                let both_pointers_case :=
                KAF_globals gv sh ls xx orig_head *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                in
                if eq_dec pa1 nullval then
                    if eq_dec pa2 nullval then
                        freelist_both_null_case
                    else freelist_only_pa1_null_case
                else 
                    if eq_dec pa2 nullval then
                        freelist_only_pa2_null_case
                    else both_pointers_case
).


Definition kfree_kalloc_kfree_kalloc_spec:= 
    DECLARE _kfree_kalloc_kfree_kalloc
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head <> nullval) /\ (r = orig_head)) \/ (* then there is exists a value or null in ls that is returned *)
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head <> nullval)) (* r is either nullval or next next*)
            ) 
            RETURN (r) (* we return the head like in the pop function*)
            SEP 
            (
                let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                (if eq_dec orig_head nullval then
                    KAF_globals gv sh ls xx orig_head * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec orig_head nullval then 
                        KAF_globals gv sh ls xx orig_head * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KAF_globals gv sh ls' xx next *
                        kalloc_token' KAF_APD sh (sizeof t_run) orig_head) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec orig_head nullval then
                        emp * KAF_globals gv sh ls xx orig_head
                    else
                        (kalloc_token' KAF_APD sh (sizeof t_run) orig_head *
                        (EX next1, EX ls1,
                        !! (next1:: ls1 = ls) &&
                        if eq_dec next1 nullval then
                            KAF_globals gv sh ls1 xx next1
                        else (
                        EX next2, EX ls2,
                        !! (next2:: ls2 = ls1) &&
                        KAF_globals gv sh ls2 xx next2 * 
                        kalloc_token' KAF_APD sh (sizeof t_run) next1
                        )))
                in
                let both_pointers_case :=
                KAF_globals gv sh ls xx orig_head *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                in
                if eq_dec pa1 nullval then
                    if eq_dec pa2 nullval then
                        freelist_both_null_case
                    else freelist_only_pa1_null_case
                else 
                    if eq_dec pa2 nullval then
                        freelist_only_pa2_null_case
                    else both_pointers_case
).

Definition kfree_kfree_kalloc_spec :=
    DECLARE _kfree_kfree_kalloc
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ r = orig_head) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ r = pa1) \/
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2)
        )
        RETURN (r) (* we return the head like in the pop function*)
        SEP 
        (
            let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                KAF_globals gv sh ls xx orig_head
            in
            let freelist_only_pa2_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                KAF_globals gv sh ls xx orig_head
            in
            let freelist_both_null_case :=
                if eq_dec orig_head nullval then
                    emp * KAF_globals gv sh ls xx orig_head
                else
                    (EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head)
            in
            let both_is_pointers_case :=
                KAF_globals gv sh (orig_head::ls) xx pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
            in

            if eq_dec pa1 nullval then
                if eq_dec pa2 nullval then
                    freelist_both_null_case
                else freelist_only_pa1_null_case
            else 
                if eq_dec pa2 nullval then
                    freelist_only_pa2_null_case
                else both_is_pointers_case
        ).

Definition kfree_kfree_kalloc_kalloc_spec := 
    DECLARE _kfree_kfree_kalloc_kalloc
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            isptr pa1 /\
            isptr pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
            kalloc_token' KAF_APD sh (sizeof t_run) pa2
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh ls xx orig_head *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                ).

Definition kfree_kfree_same_pointer_wrong_spec := 
    DECLARE _kfree_kfree_same_pointer
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1 * (* this should never happen! *)
            kalloc_token' KAF_APD sh (sizeof t_run) pa1
            )
    POST [ tvoid ]
        PROP( )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh (pa1::orig_head::ls) xx pa1
            ).

Definition kfree_kfree_same_pointer_spec := 
    DECLARE _kfree_kfree_same_pointer
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1
            )
    POST [ tvoid ]
        PROP( )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh (orig_head::ls) xx pa1
            ).

Definition KAFGprog_clients: funspecs := KAFGprog ++ [kfree_kalloc_spec].

Ltac simplify_kalloc_token :=
    repeat (
    rewrite kalloc_token_sz_unfold;
    unfold type_kalloc_token
    );
entailer!.


Lemma body_kfree_kalloc: semax_body KAFVprog KAFGprog f_kfree_kalloc kfree_kalloc_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KAF_APD t_run) (new_head, gv, sh , ls, xx, orig_head). (* call kfree *)
    + destruct (eq_dec new_head nullval).
        *unfold KAF_globals. entailer!.
        * unfold KAF_globals. entailer!. 
            simplify_kalloc_token. 
    + destruct (eq_dec new_head nullval).
        *forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head ). (* kalloc *)
        destruct (eq_dec orig_head nullval).
            --forward. Exists nullval. entailer!. unfold KAF_globals; entailer!.
            -- forward. Exists orig_head. entailer.
            Exists (fst ab) (snd ab). unfold type_kalloc_token. unfold KAF_globals. entailer!.
        * forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh, orig_head::ls, xx, new_head ). (* kalloc *)
        destruct (eq_dec new_head nullval).
            -- forward.
            -- forward. Exists new_head. entailer. inversion H0; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kfree_kalloc_inverses: semax_body KAFVprog KAFGprog f_kfree_kalloc kfree_kalloc_inverses_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KAF_APD tint) (new_head, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict.
    + rewrite H0 in H; auto_contradict.
    + unfold KAF_globals. entailer!. simplify_kalloc_token. 
- if_tac_auto_contradict.
    + rewrite H0 in H; auto_contradict.
    + forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh, orig_head::ls, xx, new_head). (* kalloc *)
      if_tac_auto_contradict; forward.
      inversion H2; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kfree_kalloc_inverses_t_run: semax_body KAFVprog KAFGprog f_kfree_kalloc kfree_kalloc_inverses_t_run_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KAF_APD t_run) (new_head, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict.
    + unfold KAF_globals. entailer!.
    + unfold KAF_globals. entailer!. simplify_kalloc_token. 
- if_tac_auto_contradict.
    + rewrite H0 in H; auto_contradict.
    + forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh, orig_head::ls, xx, new_head ). (* kalloc *)
      if_tac_auto_contradict; forward.
      inversion H2; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kfree_kalloc_inverses_tlong: semax_body KAFVprog KAFGprog f_kfree_kalloc kfree_kalloc_inverses_tlong_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KAF_APD tlong) (new_head, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict.
    + unfold KAF_globals. entailer!.
    + unfold KAF_globals. entailer!. simplify_kalloc_token. 
- if_tac_auto_contradict.
    + rewrite H0 in H; auto_contradict.
    + forward_call (kalloc_spec_sub KAF_APD tlong) (gv, sh, orig_head::ls, xx, new_head ). (* kalloc *)
      if_tac_auto_contradict; forward.
      inversion H2; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kalloc_kfree_inverses: semax_body KAFVprog KAFGprog f_kalloc_kfree kalloc_kfree_inverses_spec.
Proof.
start_function.
forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head).
- unfold KAF_globals. entailer!.
- if_tac.
    + forward_call (kfree_spec_sub KAF_APD t_run) (nullval, gv, sh , ls, xx, orig_head).
        * if_tac_auto_contradict. entailer!.
        * if_tac_auto_contradict. unfold KAF_globals. entailer!.
    + Intros ab. assert_PROP(isptr orig_head).
        * unfold type_kalloc_token. entailer!.
        * forward_call (kfree_spec_sub KAF_APD t_run) (orig_head, gv, sh , snd ab, xx, fst ab).
        -- if_tac_auto_contradict. entailer!.
        -- if_tac_auto_contradict. unfold KAF_globals. entailer!.
Qed.

Lemma body_kalloc_write_42_kfree: semax_body KAFVprog KAFGprog f_kalloc_write_42_kfree kalloc_write_42_kfree_spec.
Proof.
start_function.
Intros.
forward.
- forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, orig_head ). (* kalloc *)
+ unfold KAF_globals. entailer!.
+ if_tac_auto_contradict.
    * forward_if.
        -- rewrite H in H0; auto_contradict.
        -- forward. Exists (Vint(Int.repr 0)). entailer.
    * Intros ab.
    destruct ls; auto_contradict.
    forward_if.
      -- unfold type_kalloc_token. rewrite kalloc_token_sz_unfold.
      destruct orig_head eqn:eo; inversion H0; auto_contradict.
      assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus). { Intros. entailer!. }
      rewrite token_merge with (b:= b) (i:= i); auto.
      2: { try rep_lia. }
      Intros.
      rewrite <- token_merge_size with (b:= b) (i:= i) (sz:=sizeof tint); auto; try rep_lia.
      rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
      repeat forward.
      forward_call (kfree_spec_sub KAF_APD tint) (Vptr b i, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        ++ if_tac_auto_contradict.
            unfold type_kalloc_token. rewrite kalloc_token_sz_unfold. entailer!.
            sep_apply data_at_memory_block. 
            rewrite token_merge with (b:= b) (i:= i); auto; try rep_lia.
            rewrite <- token_merge_size with (b:= b) (i:= i) (sz:=sizeof tint); auto; try rep_lia.
            entailer!.
        ++ if_tac_auto_contradict.
            forward. Exists (Vint (Int.repr 42)). unfold KAF_globals. entailer.
        -- forward.
Qed.
        
Lemma body_kfree_kalloc_twice: semax_body KAFVprog KAFGprog_clients f_kfree_kalloc_twice kfree_kalloc_twice_spec.
Proof.
start_function. destruct H.
forward_call (gv, sh, pa1, orig_head, xx, ls).
- entailer!.
- Intros vret.
    if_tac.
    + if_tac.
        * if_tac.
            -- forward_call (gv, sh, pa2, orig_head, xx, ls).
                ++ if_tac_auto_contradict.
                    entailer!.
                ++ if_tac_auto_contradict. Intros vret0.
                    if_tac_auto_contradict.
                    forward.
                    Exists vret0. entailer!.
                    destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
            --forward_call (gv, sh, pa2, orig_head, xx, ls).
                ++ if_tac_auto_contradict. entailer!.
                ++ if_tac_auto_contradict. Intros vret0. forward.
                    Exists vret0. entailer!.
                    destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict. do 4 right. left. auto.
        * if_tac; Intros ab.
            -- destruct ls as [ | next1 ls1]; auto_contradict. (*unfold abbreviate in POSTCONDITION.*)
                forward_call (gv, sh, pa2, next1, xx, ls1).
                ++ if_tac_auto_contradict.
                inversion H5. rewrite H8; rewrite H9. entailer!.
                ++ if_tac_auto_contradict. if_tac_auto_contradict. 
                    ** Intros vret0. forward.
                    Exists vret0. Exists nullval ls1. if_tac_auto_contradict. entailer!.
                    destruct H8 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict. 
                    do 5 right. split; auto.
                    ** Intros vret0. Intros ab0. forward.
                    Exists vret0. Exists (next1) (snd ab). if_tac_auto_contradict.
                    Exists (fst ab0) (snd ab0). entailer!.
                    do 5 right. split; auto.
            -- destruct ls as [ | next1 ls1]; auto_contradict. 
                forward_call (gv, sh, pa2, next1, xx, ls1).
                ++ if_tac_auto_contradict.
                inversion H5. rewrite H8; rewrite H9. entailer!.
                ++ Intros vret0. forward. if_tac_auto_contradict.
                Exists vret0. Exists next1 ls1. entailer!.
                destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict. 
                do 4 right. left; split; auto.
    + if_tac.
        -- forward_call (gv, sh, pa2, orig_head, xx, ls).
            ++ if_tac_auto_contradict.
                entailer!.
            ++ if_tac_auto_contradict. Intros vret0.
                if_tac_auto_contradict.
                ** forward. 
                Exists vret0. entailer!.
                destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
                do 2 right. left. split; auto.
                ** Intros ab.
                    forward. Exists vret0. Exists (fst ab) (snd ab). entailer!.
                    destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
                    do 2 right. left; split; auto.
                    do 3 right. left; split; auto.
        -- Intros. forward_call (gv, sh, pa2, orig_head, xx, ls).
            ++ if_tac_auto_contradict. entailer!.
            ++ if_tac_auto_contradict. 
                Intros vret0. forward.
                Exists vret0. entailer!.
                destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict.
                ** right. left; split; auto.
Qed.
        
        
Lemma body_kfree_kalloc_kfree_kalloc: semax_body KAFVprog KAFGprog f_kfree_kalloc_kfree_kalloc kfree_kalloc_kfree_kalloc_spec.
Proof.
start_function. Intros.
if_tac; if_tac; destruct H; 
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict. unfold KAF_globals. entailer!. (* kfree's precondition is met, when both pa1 and pa2 is null *)
- forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
    + if_tac_auto_contradict. entailer!. (* kalloc's preconditions are met, when both pa1 and pa2 is null *)
    + if_tac_auto_contradict.
        * forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx, orig_head). (* call kfree *)
            -- if_tac_auto_contradict. entailer!. (* kfree's precondition is met, when both pa1 and pa2 is null *)
            -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc, its precondition is automatically met *)
                if_tac_auto_contradict.
                forward. Exists nullval; unfold KAF_globals. entailer!.
        * Intros ab. destruct ls; auto_contradict. (* there are elements in the freelist*)
        forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
            -- entailer!. (* the precondition is met *)
            -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
                if_tac.
                    ++ forward. Exists (fst ab) (fst ab) (snd ab). if_tac.
                        ** unfold KAF_globals. unfold type_kalloc_token. entailer!. repeat right. split; auto.
                        ** entailer.
                    ++ Intros ab0. forward. Exists (fst ab). unfold type_kalloc_token. rewrite mem_mgr_unfold. 
                        Exists (fst ab) (snd ab). if_tac_auto_contradict. Exists (fst ab0) (snd ab0). rewrite mem_mgr_unfold; entailer!.
                        repeat right; split; auto.
- if_tac_auto_contradict. unfold KAF_globals. entailer!.
- forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. 
    * forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx, orig_head). (* call kfree *)
        -- if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
        -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , (orig_head :: ls), xx, pa2). (* kalloc *)
            if_tac.
                ++ forward.
                ++ Intros ab. destruct ls; auto_contradict;
                    forward; unfold type_kalloc_token, KAF_globals; inversion H6; rewrite H3; rewrite H9; Exists pa2; entailer!;
                    do 4 right; left; split; auto.
    * Intros ab. destruct ls; auto_contradict.  
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
        -- if_tac_auto_contradict. unfold type_kalloc_token at 2. rewrite kalloc_token_sz_unfold. entailer!.
        -- if_tac_auto_contradict. rewrite mem_mgr_unfold. Intros. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
            ++ unfold type_kalloc_token. rewrite mem_mgr_unfold.  entailer!.
            ++ forward. if_tac_auto_contradict. Intros ab0. Exists pa2 (fst ab0) (snd ab0). rewrite mem_mgr_unfold. unfold KAF_globals, type_kalloc_token. rewrite mem_mgr_unfold. entailer!.
                do 4 right. left; split; auto.
- if_tac_auto_contradict. unfold KAF_globals. rewrite kalloc_token_sz_unfold. unfold type_kalloc_token. rewrite kalloc_token_sz_unfold. entailer!.
- if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    ++ entailer!.
    ++ if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
        forward. if_tac_auto_contradict; inversion H5.
        ** Exists (fst ab). if_tac_auto_contradict.
        unfold type_kalloc_token, KAF_globals. entailer!.
        do 2 right; left; split; auto.
        ** Intros ab0. Exists (fst ab). if_tac_auto_contradict.
            Exists (fst ab0) (snd ab0). unfold type_kalloc_token, KAF_globals. entailer!.
            do 3 right; left; split; auto.
- if_tac_auto_contradict. unfold KAF_globals. unfold type_kalloc_token. entailer!.
- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    + if_tac_auto_contradict. unfold type_kalloc_token at 2; entailer!.
    + if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab0. forward. Exists pa2. unfold KAF_globals. unfold type_kalloc_token; entailer!.
    inversion H8. rewrite H14, H15. inversion H5. entailer!.
        Qed.
        
Lemma body_kfree_kfree_kalloc: semax_body KAFVprog KAFGprog f_kfree_kfree_kalloc kfree_kfree_kalloc_spec.
Proof.
start_function.
Intros.
if_tac; if_tac; destruct H; 
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict. unfold KAF_globals. entailer!.
- if_tac_auto_contradict;
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx, orig_head). (* call kfree*)
    + if_tac_auto_contradict. entailer!.
    + if_tac_auto_contradict.
        forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
        if_tac_auto_contradict. 
        * forward. Exists nullval. unfold KAF_globals. entailer!.
        * forward. Exists orig_head. Exists (fst ab) (snd ab). entailer!. 
        unfold type_kalloc_token, KAF_globals. entailer!.
-if_tac_auto_contradict. unfold KAF_globals. entailer!.
-if_tac_auto_contradict;
forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx,orig_head). (* call kfree*)
+ if_tac_auto_contradict. entailer!. unfold type_kalloc_token; entailer!. 
+ if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. 
    forward. Exists pa2. unfold KAF_globals. entailer!.
        * do 3 right. split; auto.
        * unfold type_kalloc_token. entailer!. inversion H0. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold KAF_globals, type_kalloc_token. entailer!.
- if_tac_auto_contradict. 
forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , orig_head::ls, xx,pa1). (* call kfree*)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab. forward. Exists pa1. unfold type_kalloc_token, KAF_globals. entailer!.
    * do 2 right; left; split; auto.
    * inversion H6. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold type_kalloc_token, KAF_globals. entailer!.
- if_tac_auto_contradict. forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , orig_head::ls, xx,pa1). (* call kfree*)
    + if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
    + if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , pa1::orig_head::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. Intros ab.
    forward. Exists pa2. unfold KAF_globals, type_kalloc_token. entailer!.
    inversion H6.
    entailer.
Qed.


Lemma body_kfree_kfree_kalloc_kalloc: semax_body KAFVprog KAFGprog f_kfree_kfree_kalloc_kalloc kfree_kfree_kalloc_kalloc_spec.
Proof.
start_function.
Intros.
destruct H. 
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- unfold KAF_globals.
    if_tac.
    + rewrite H1 in H. auto_contradict.
    + unfold type_kalloc_token. entailer!. 
- if_tac_auto_contradict. rewrite H1 in H. auto_contradict.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , orig_head::ls, xx, pa1).
    if_tac_auto_contradict. rewrite H2 in H0; auto_contradict.
    unfold type_kalloc_token.
    entailer!.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , pa1::orig_head::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict; entailer!.
    if_tac_auto_contradict. rewrite H2 in H0; auto_contradict.
    Intros ab. 
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    inversion H3. entailer!.
    if_tac_auto_contradict.
    Intros ab0. 
    forward. unfold type_kalloc_token. entailer!. unfold KAF_globals. inversion H5; entailer.
Qed.

Lemma body_kfree_kfree_same_wrong_pointer: semax_body KAFVprog KAFGprog f_kfree_kfree_same_pointer kfree_kfree_same_pointer_wrong_spec.
Proof.
start_function.
Intros.
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- unfold KAF_globals.
    if_tac.
    + rewrite H0 in H. auto_contradict.
    + unfold type_kalloc_token. entailer!. 
- if_tac_auto_contradict. rewrite H0 in H. auto_contradict.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , orig_head::ls, xx, pa1).
    +  if_tac_auto_contradict.
    unfold type_kalloc_token.
    entailer!.
    + if_tac_auto_contradict.
      entailer. 
Qed.

Lemma is_writable_implies_nonidentity :
  forall sh : share,
  writable_share sh -> 
    sepalg.nonidentity sh.
Proof.
  intros sh H.
  unfold sepalg.nonidentity.
  intros Hid.
  apply identity_share_bot in Hid.
  subst.
  unfold writable_share in H.
  destruct H as [Hglb Hsub].
  unfold nonempty_share in Hglb.
  unfold sepalg.nonidentity in Hglb.
  apply Hglb.
  rewrite Share.glb_bot.
  auto.
Qed.  

Lemma data_at_same_ptr_diff_val :
  forall (sh : share) (p : val) t v1 v2,
    writable_share sh -> 
    0 < sizeof t ->
    (data_at sh t v1 p * data_at sh t v2 p) |-- FF.
Proof.
    intros.
    apply data_at_conflict.
    - apply is_writable_implies_nonidentity; auto.
    - auto.
Qed. 

Lemma body_kfree_kfree_same_wrong_pointer': semax_body KAFVprog KAFGprog f_kfree_kfree_same_pointer kfree_kfree_same_pointer_wrong_spec.
Proof.
    start_function.
    Intros.
    rewrite kalloc_token_sz_unfold. Intros.
    assert (memory_block sh t_run_size pa1 = data_at_ sh t_run pa1) as HH7. {
        unfold t_run_size; rewrite memory_block_data_at_ with (sh := sh) (t:= t_run) (p:=pa1); auto.
    }
    rewrite data_at__eq in HH7. rewrite HH7.
    sep_apply data_at_same_ptr_diff_val.
    repeat (sep_apply FF_sepcon). (* FF in SEP *)
Abort.

Lemma body_kfree_kfree_same_pointer: semax_body KAFVprog KAFGprog f_kfree_kfree_same_pointer kfree_kfree_same_pointer_spec.
Proof.
start_function.
Intros.
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- unfold KAF_globals.
    if_tac.
    + rewrite H0 in H. auto_contradict.
    + unfold type_kalloc_token. entailer!. 
- if_tac_auto_contradict. rewrite H0 in H. auto_contradict.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , orig_head::ls, xx, pa1).
    + if_tac_auto_contradict. entailer!.
     (* a token needs to be included in the pre-condition for being able to call kfree *) admit.
    + if_tac_auto_contradict.
      unfold KAF_globals. entailer!. 
      (* TThe precondition for kfree is expected to include more information,
            but it is incomplete in this case. This leads to a wrong call to kfree,
            causing a wrong memory amanger and leftover memory that should have been freed. *)
Abort.