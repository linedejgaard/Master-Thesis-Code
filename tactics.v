Require Import VST.floyd.proofauto.

(* ================================================================= *)
(** ** Helper functions and tactics *)

Ltac auto_contradict := try discriminate; try contradiction.

Ltac if_tac_auto_contradict :=
  if_tac; auto_contradict.