From Coq Require Import Unicode.Utf8.

Theorem plus_one_r' : ∀ n:nat,
  n + 1 = S n.
Proof.
    apply nat_ind.
    reflexivity.
    intros.
    simpl.
    rewrite <- H.
    reflexivity.
    Qed.

Inductive booltree : Type :=
    | bt_empty
    | bt_leaf (b : bool)
    | bt_branch (b : bool) (t1 t2 : booltree).

