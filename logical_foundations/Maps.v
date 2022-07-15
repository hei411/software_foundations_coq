From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Unicode.Utf8.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : ∀ s : string, true = eqb_string s s.
Proof.
    intros s.
    unfold eqb_string.
    destruct (string_dec s s) as [H|H].
    reflexivity.
    destruct H.
    auto.
    Qed.

Theorem eqb_string_true_iff : ∀ x y : string,
    eqb_string x y = true ↔ x = y.
Proof.
    intros x y.
    split.
    intros H.
    unfold eqb_string in H.
    destruct (string_dec _ _)  eqn:E in H.
    assumption.
    inversion H.
    intros H.
    unfold eqb_string.
    destruct (string_dec _ _) eqn:E .
    reflexivity.
    apply n in H.
    auto.
    Qed.

Theorem eqb_string_false_iff : ∀ x y : string,
    eqb_string x y = false ↔ x ≠ y.

Proof.
    intros x y.
    rewrite <- eqb_string_true_iff.
    rewrite not_true_iff_false.
    reflexivity.
Qed.


Definition total_map (A : Type) := string → A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v ) .
Definition t_update {A : Type} (m : total_map A)
  (x : string) (v : A) :=
fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
(at level 100, v at next level, right associativity).

Lemma eqb_stringP : ∀ x y : string,
  reflect (x = y) (eqb_string x y).
Proof.
    intros x y.
    apply iff_reflect.
    rewrite eqb_string_true_iff.
    reflexivity.
    Qed.




Theorem t_update_same : ∀ (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
    intros A m x.
    unfold t_update.
    apply functional_extensionality.
    intros x0.
    destruct (eqb_string _ _) eqn:E.
    destruct (eqb_stringP x x0) as [a|b] in E.
    rewrite a. reflexivity.
    inversion E.
    reflexivity.
    Qed.

 Theorem t_update_permute : ∀ (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 ≠ x1 →
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
    intros.
    unfold t_update.
    apply functional_extensionality.
    intros.
    destruct (eqb_string x1 x) eqn:E1.
    destruct (eqb_string x2 x) eqn:E2.
    destruct (eqb_stringP x1 x) in E1.
    rewrite e in H.
    destruct (eqb_stringP x2 x) in E2.
    rewrite e0 in H.
    exfalso.
    apply H.
    reflexivity.
    inversion E2.
    inversion E1.
    reflexivity.
    reflexivity.
    Qed.

    Definition partial_map (A : Type) := total_map (option A).
    Definition empty {A : Type} : partial_map A :=
      t_empty None.
    Definition update {A : Type} (m : partial_map A)
               (x : string) (v : A) :=
      (x !-> Some v ; m).

      Notation "x '⊢>' v ';' m" := (update m x v)
      (at level 100, v at next level, right associativity).
      Notation "x '⊢>' v" := (update empty x v)
  (at level 100).
Example examplepmap :=
  ("Church" ⊢> true ; "Turing" ⊢> false).

  Lemma apply_empty : ∀ (A : Type) (x : string),
  @empty A x = None.
  intros.
  unfold empty.
  unfold t_empty.
  reflexivity.

  Qed.
  Lemma update_eq : ∀ (A : Type) (m : partial_map A) x v,
  (x ⊢> v ; m) x = Some v.
  Proof.
    intros.
    unfold update.
    unfold t_update.
    rewrite <-eqb_string_refl.
    reflexivity.
    
    Qed.

    Theorem update_neq : ∀ (A : Type) (m : partial_map A) x1 x2 v,
  x2 ≠ x1 →
  (x2 ⊢> v ; m) x1 = m x1.
  Proof.
    intros.
    unfold update. unfold t_update.
    destruct (eqb_stringP x2 x1).
    apply H in e.
    destruct e.
    reflexivity.
    Qed.

    Lemma update_shadow : ∀ (A : Type) (m : partial_map A) x v1 v2,
    (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m).
    Proof.
        intros.
        unfold update.
        unfold t_update.
        apply functional_extensionality. intros.
        destruct (eqb_string x x0).
        reflexivity.
        reflexivity.
        Qed.

Theorem update_same : ∀ (A : Type) (m : partial_map A) x v,
        m x = Some v →
        (x ⊢> v ; m) = m.

    Proof.
        intros.
        unfold update. unfold t_update.
        apply functional_extensionality.
        intros.
        destruct (eqb_string x x0) eqn:E.
        rewrite <-H.
        rewrite eqb_string_true_iff in E.
        rewrite E.
        reflexivity. reflexivity.
        Qed.

        Theorem update_permute : ∀ (A : Type) (m : partial_map A)
        x1 x2 v1 v2,
x2 ≠ x1 →
(x1 ⊢> v1 ; x2 ⊢> v2 ; m) = (x2 ⊢> v2 ; x1 ⊢> v1 ; m).
intros.
unfold update.
apply t_update_permute.
assumption.
Qed.

Definition inclusion {A : Type} (m m' : partial_map A) :=
  ∀ x v, m x = Some v → m' x = Some v.

  Lemma inclusion_update : ∀ (A : Type) (m m' : partial_map A)
  (x : string) (vx : A),
inclusion m m' →
inclusion (x ⊢> vx ; m) (x ⊢> vx ; m').
Proof.
    unfold inclusion.
    intros.
    destruct (eqb_stringP x x0) as [a|b].
    rewrite<-a. 
    rewrite update_eq.
    rewrite a in H0.
    rewrite update_eq in H0.
    assumption.
    rewrite update_neq.
    apply H.
    rewrite update_neq in H0.
    assumption.
    assumption.
    assumption.
    Qed.