From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "kalloc.c".
  Definition normalized := true.
End Info.

Definition _X : ident := $"X".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _data : ident := $"data".
Definition _freelist : ident := $"freelist".
Definition _i : ident := $"i".
Definition _kalloc : ident := $"kalloc".
Definition _kalloc_int_array : ident := $"kalloc_int_array".
Definition _kalloc_kfree : ident := $"kalloc_kfree".
Definition _kalloc_write_42 : ident := $"kalloc_write_42".
Definition _kalloc_write_42_kfree : ident := $"kalloc_write_42_kfree".
Definition _kalloc_write_pipe : ident := $"kalloc_write_pipe".
Definition _kfree : ident := $"kfree".
Definition _kfree_kalloc : ident := $"kfree_kalloc".
Definition _kfree_kalloc_kfree_kalloc : ident := $"kfree_kalloc_kfree_kalloc".
Definition _kfree_kalloc_twice : ident := $"kfree_kalloc_twice".
Definition _kfree_kfree_kalloc : ident := $"kfree_kfree_kalloc".
Definition _kfree_kfree_kalloc_kalloc : ident := $"kfree_kfree_kalloc_kalloc".
Definition _kfree_kfree_kalloc_loop : ident := $"kfree_kfree_kalloc_loop".
Definition _kfree_kfree_same_pointer : ident := $"kfree_kfree_same_pointer".
Definition _kfree_loop : ident := $"kfree_loop".
Definition _kfree_loop_kalloc : ident := $"kfree_loop_kalloc".
Definition _kmem : ident := $"kmem".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _next : ident := $"next".
Definition _nread : ident := $"nread".
Definition _nwrite : ident := $"nwrite".
Definition _p : ident := $"p".
Definition _pa : ident := $"pa".
Definition _pa1 : ident := $"pa1".
Definition _pa2 : ident := $"pa2".
Definition _pa_start : ident := $"pa_start".
Definition _pi : ident := $"pi".
Definition _pipe : ident := $"pipe".
Definition _r : ident := $"r".
Definition _readopen : ident := $"readopen".
Definition _run : ident := $"run".
Definition _struct_kmem : ident := $"struct_kmem".
Definition _writeopen : ident := $"writeopen".
Definition _xx : ident := $"xx".
Definition _t'1 : ident := 128%positive.

Definition v_kmem := {|
  gvar_info := (Tstruct _struct_kmem noattr);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_kfree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _run noattr))) ::
               (_t'1, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool (Etempvar _pa (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sset _r
      (Ecast (Etempvar _pa (tptr tvoid)) (tptr (Tstruct _run noattr))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
            (tptr (Tstruct _run noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _run noattr)))
              (Tstruct _run noattr)) _next (tptr (Tstruct _run noattr)))
          (Etempvar _t'1 (tptr (Tstruct _run noattr)))))
      (Sassign
        (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
          (tptr (Tstruct _run noattr)))
        (Etempvar _r (tptr (Tstruct _run noattr)))))))
|}.

Definition f_kalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _run noattr))) ::
               (_t'1, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _r
    (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
      (tptr (Tstruct _run noattr))))
  (Ssequence
    (Sifthenelse (Etempvar _r (tptr (Tstruct _run noattr)))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _run noattr)))
              (Tstruct _run noattr)) _next (tptr (Tstruct _run noattr))))
        (Sassign
          (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
            (tptr (Tstruct _run noattr)))
          (Etempvar _t'1 (tptr (Tstruct _run noattr)))))
      Sskip)
    (Sreturn (Some (Ecast (Etempvar _r (tptr (Tstruct _run noattr)))
                     (tptr tvoid))))))
|}.

Definition f_kalloc_write_42 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_pa, (tptr tint)) :: (_X, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _pa (Ecast (Econst_int (Int.repr 0) tint) (tptr tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Sset _pa (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
    (Ssequence
      (Sifthenelse (Etempvar _pa (tptr tint))
        (Ssequence
          (Sassign (Ederef (Etempvar _pa (tptr tint)) tint)
            (Econst_int (Int.repr 42) tint))
          (Ssequence
            (Sset _X (Ederef (Etempvar _pa (tptr tint)) tint))
            (Sreturn (Some (Etempvar _X tint)))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_kalloc_int_array := {|
  fn_return := (tptr tint);
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, (tptr tint)) :: (_i, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _pa (Ecast (Econst_int (Int.repr 0) tint) (tptr tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Sset _pa (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
    (Ssequence
      (Sifthenelse (Etempvar _pa (tptr tint))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _n tint) tint)
                  Sskip
                  Sbreak)
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _pa (tptr tint))
                      (Etempvar _i tint) (tptr tint)) tint)
                  (Econst_int (Int.repr 42) tint)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Sreturn (Some (Etempvar _pa (tptr tint)))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_kalloc_write_pipe := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_pi, (tptr (Tstruct _pipe noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _pi
    (Ecast (Econst_int (Int.repr 0) tint) (tptr (Tstruct _pipe noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Sset _pi
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _pipe noattr)))))
    (Sifthenelse (Etempvar _pi (tptr (Tstruct _pipe noattr)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _pi (tptr (Tstruct _pipe noattr)))
              (Tstruct _pipe noattr)) _readopen tint)
          (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _pi (tptr (Tstruct _pipe noattr)))
                (Tstruct _pipe noattr)) _writeopen tint)
            (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _pi (tptr (Tstruct _pipe noattr)))
                  (Tstruct _pipe noattr)) _nwrite tint)
              (Econst_int (Int.repr 0) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _pi (tptr (Tstruct _pipe noattr)))
                  (Tstruct _pipe noattr)) _nread tint)
              (Econst_int (Int.repr 0) tint)))))
      Sskip)))
|}.

Definition f_kfree_kalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa (tptr tvoid)) :: nil))
  (Ssequence
    (Scall (Some _t'1) (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default))
      nil)
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_kalloc_kfree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default))
      nil)
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _p (tptr tvoid)) :: nil)))
|}.

Definition f_kalloc_write_42_kfree := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_pa, (tptr tint)) :: (_X, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _pa (Ecast (Econst_int (Int.repr 0) tint) (tptr tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Sset _pa (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
    (Ssequence
      (Sifthenelse (Etempvar _pa (tptr tint))
        (Ssequence
          (Sassign (Ederef (Etempvar _pa (tptr tint)) tint)
            (Econst_int (Int.repr 42) tint))
          (Ssequence
            (Sset _X (Ederef (Etempvar _pa (tptr tint)) tint))
            (Ssequence
              (Scall None
                (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid
                               cc_default))
                ((Etempvar _pa (tptr tint)) :: nil))
              (Sreturn (Some (Etempvar _X tint))))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_kfree_kalloc_twice := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa1, (tptr tvoid)) :: (_pa2, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree_kalloc (Tfunction ((tptr tvoid) :: nil) (tptr tvoid)
                          cc_default)) ((Etempvar _pa1 (tptr tvoid)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _kfree_kalloc (Tfunction ((tptr tvoid) :: nil) (tptr tvoid)
                            cc_default))
      ((Etempvar _pa2 (tptr tvoid)) :: nil))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_kfree_kalloc_kfree_kalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa1, (tptr tvoid)) :: (_pa2, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa1 (tptr tvoid)) :: nil))
  (Ssequence
    (Scall None (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
    (Ssequence
      (Scall None
        (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
        ((Etempvar _pa2 (tptr tvoid)) :: nil))
      (Ssequence
        (Scall (Some _t'1)
          (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
        (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))))
|}.

Definition f_kfree_kfree_kalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa1, (tptr tvoid)) :: (_pa2, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa1 (tptr tvoid)) :: nil))
  (Ssequence
    (Scall None
      (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _pa2 (tptr tvoid)) :: nil))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))))
|}.

Definition f_kfree_kfree_kalloc_kalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa1, (tptr tvoid)) :: (_pa2, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa1 (tptr tvoid)) :: nil))
  (Ssequence
    (Scall None
      (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _pa2 (tptr tvoid)) :: nil))
    (Ssequence
      (Scall None (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
        (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))))
|}.

Definition f_kfree_kfree_same_pointer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa1, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa1 (tptr tvoid)) :: nil))
  (Scall None
    (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa1 (tptr tvoid)) :: nil)))
|}.

Definition f_kfree_kfree_kalloc_loop := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Swhile
      (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 2) tint) tint)
      (Ssequence
        (Scall None
          (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
          ((Etempvar _pa_start (tptr tvoid)) :: nil))
        (Ssequence
          (Sset _pa_start
            (Ebinop Oadd
              (Ecast (Etempvar _pa_start (tptr tvoid)) (tptr tschar))
              (Econst_int (Int.repr 4096) tint) (tptr tschar)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default)) nil)
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))))
|}.

Definition f_kfree_loop := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Swhile
    (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint) tint)
    (Ssequence
      (Scall None
        (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
        ((Etempvar _pa_start (tptr tvoid)) :: nil))
      (Ssequence
        (Sset _pa_start
          (Ebinop Oadd
            (Ecast (Etempvar _pa_start (tptr tvoid)) (tptr tschar))
            (Econst_int (Int.repr 4096) tint) (tptr tschar)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_kfree_loop_kalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kfree_loop (Tfunction ((tptr tvoid) :: tint :: nil) tvoid
                        cc_default))
    ((Etempvar _pa_start (tptr tvoid)) :: (Etempvar _n tint) :: nil))
  (Ssequence
    (Scall (Some _t'1) (Evar _kalloc (Tfunction nil (tptr tvoid) cc_default))
      nil)
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition composites : list composite_definition :=
(Composite _run Struct
   (Member_plain _next (tptr (Tstruct _run noattr)) :: nil)
   noattr ::
 Composite _struct_kmem Struct
   (Member_plain _xx tint ::
    Member_plain _freelist (tptr (Tstruct _run noattr)) :: nil)
   noattr ::
 Composite _pipe Struct
   (Member_plain _data (tarray tschar 512) :: Member_plain _nread tint ::
    Member_plain _nwrite tint :: Member_plain _readopen tint ::
    Member_plain _writeopen tint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_kmem, Gvar v_kmem) :: (_kfree, Gfun(Internal f_kfree)) ::
 (_kalloc, Gfun(Internal f_kalloc)) ::
 (_kalloc_write_42, Gfun(Internal f_kalloc_write_42)) ::
 (_kalloc_int_array, Gfun(Internal f_kalloc_int_array)) ::
 (_kalloc_write_pipe, Gfun(Internal f_kalloc_write_pipe)) ::
 (_kfree_kalloc, Gfun(Internal f_kfree_kalloc)) ::
 (_kalloc_kfree, Gfun(Internal f_kalloc_kfree)) ::
 (_kalloc_write_42_kfree, Gfun(Internal f_kalloc_write_42_kfree)) ::
 (_kfree_kalloc_twice, Gfun(Internal f_kfree_kalloc_twice)) ::
 (_kfree_kalloc_kfree_kalloc, Gfun(Internal f_kfree_kalloc_kfree_kalloc)) ::
 (_kfree_kfree_kalloc, Gfun(Internal f_kfree_kfree_kalloc)) ::
 (_kfree_kfree_kalloc_kalloc, Gfun(Internal f_kfree_kfree_kalloc_kalloc)) ::
 (_kfree_kfree_same_pointer, Gfun(Internal f_kfree_kfree_same_pointer)) ::
 (_kfree_kfree_kalloc_loop, Gfun(Internal f_kfree_kfree_kalloc_loop)) ::
 (_kfree_loop, Gfun(Internal f_kfree_loop)) ::
 (_kfree_loop_kalloc, Gfun(Internal f_kfree_loop_kalloc)) :: nil).

Definition public_idents : list ident :=
(_kfree_loop_kalloc :: _kfree_loop :: _kfree_kfree_kalloc_loop ::
 _kfree_kfree_same_pointer :: _kfree_kfree_kalloc_kalloc ::
 _kfree_kfree_kalloc :: _kfree_kalloc_kfree_kalloc :: _kfree_kalloc_twice ::
 _kalloc_write_42_kfree :: _kalloc_kfree :: _kfree_kalloc ::
 _kalloc_write_pipe :: _kalloc_int_array :: _kalloc_write_42 :: _kalloc ::
 _kfree :: _kmem :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


