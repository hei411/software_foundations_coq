Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Unicode.Utf8.
From LF Require Export Indprop.

Module MyEquality.
Inductive eq {X:Type} : X → X → Prop :=
  | eq_refl : ∀ x, eq x x.
Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

Lemma equality__leibniz_equality : ∀ (X : Type) (x y: X),
  x == y → ∀ P:X→Prop, P x → P y.
Proof.
    intros.
    inversion H.
    rewrite <-H2.
    assumption.
    Qed.

Lemma leibniz_equality__equality : ∀ (X : Type) (x y: X),
  (∀ P:X→Prop, P x → P y) → x == y.
Proof.
    intros.
    apply H.
    apply eq_refl.
    Qed.

    End MyEquality.
    
