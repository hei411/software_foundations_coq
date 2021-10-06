Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
  
  Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
intros.
induction n.
simpl.
apply ev_0.
simpl.
apply ev_SS.
exact IHn.
Qed.

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem  evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
  Proof.
  intros n E.
  remember (S (S n)) as k eqn:Hk.
  destruct E as [|n' E'] eqn:EE.
  discriminate Hk.
  injection Hk as Heq.
  rewrite <- Heq.
  exact E'.
  Qed.
  
Theorem evSS_ev : forall n, ev (S (S n))-> ev n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
    - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.
  
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H. inversion H1.
  exact H3.
  Qed.
Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
  Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.
  
Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.
  
Lemma ev_Even : forall  n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even E' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros.
induction H.
apply H0.
simpl.
apply ev_SS.
apply IHev.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
intros.
induction H0.
simpl in H.
exact H.
simpl in H.

inversion H.
apply IHev in H2.
exact H2.
Qed.

Module Playground.
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "n <= m" := (le n m).

Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).
End Playground.
 
 
Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).
Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).
Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n)) : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).
  
Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o
.


Inductive subseq : list nat -> list nat -> Prop :=
| empty k: subseq [] k
| extend a b c (H:subseq a b): subseq a (c::b)
| same a b c (H:subseq a b): subseq (c::a) (c::b)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
intros.
induction l.
apply (empty []).
apply (same).
apply IHl.
Qed.

Lemma lemma1: forall (x:nat) l1 l2, (x::l1) ++ l2 = x::(l1++l2).
intros.
induction l1.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2->
  subseq l1 (l2 ++ l3).
Proof.
intros.
induction H.
apply empty.
rewrite lemma1.
apply extend.
exact IHsubseq.
rewrite lemma1.
apply same.
exact IHsubseq.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
intros.
generalize dependent l1.
induction H0.
intros.
inversion H.
apply empty.
intros.
apply extend.
apply IHsubseq in H.
exact H.
intros.
inversion H.
apply empty.
apply extend.
apply IHsubseq.
apply H3.
apply same.
apply IHsubseq.
apply H3.
Qed.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
  
  Lemma MStar1 :
 forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
    Proof.
    intros.
    assert (forall X (l:list X), l++[] = l).
    induction l.
    reflexivity.
    simpl.
    rewrite IHl.
    reflexivity.
    rewrite <- (H0 T s).
    apply (MStarApp s [] re).
    exact H.
    apply MStar0.
    Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros.
  unfold not.
  intros.
  inversion H.
  Qed.
Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  apply MUnionL.
  exact H.
  apply MUnionR.
  exact H.
  Qed.
  
  
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  simpl.
  apply MStar0.
  simpl.
  apply MStarApp.
  apply H.
  simpl.
  left.
  reflexivity.
  apply IHss.
  intros.
  apply H.
  simpl.
  right.
  apply H0.
  Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
match re with 
|EmptySet => false
|EmptyStr => true
|Char _ => true
| App r1 r2 => re_not_empty r1 && re_not_empty r2
| Union r1 r2 => re_not_empty r1 ||re_not_empty r2
|Star _ => true
end.


Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros.
  split.
  intros.
  destruct H.
  induction H.
  reflexivity.
  reflexivity.
  simpl.
  rewrite IHexp_match1, IHexp_match2.
  reflexivity.
  simpl.
  rewrite IHexp_match.
  reflexivity.
  simpl.
  rewrite IHexp_match.
  destruct (re_not_empty re1).
  reflexivity.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  intros.
  induction re.
  simpl in H.
  discriminate H.
  exists [].
  apply MEmpty.
  exists [t].
  apply MChar.
  simpl in H.
  apply andb_true_iff in H.
  destruct H.
  apply IHre1 in H.
  apply IHre2 in H0.
  destruct H.
  destruct H0.
  exists (x++x0).
  apply MApp.
  exact H.
  exact H0.
  simpl in H.
  apply orb_true_iff in H.
  destruct H.
  apply IHre1 in H.
  destruct H.
  exists x.
  apply MUnionL.
  exact H.
  apply IHre2 in H.
  destruct H.
  exists x.
  apply MUnionR.
  exact H.
  exists [].
  apply MStar0.
  Qed.
  
  
  Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~P) : reflect P false.  
  
Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  split.
  intros.
  inversion H.
  reflexivity.
  unfold not in H1.
  apply H1 in H0.
  destruct H0.
  intros.
  rewrite H0 in H.
  inversion H.
  exact H1.
  Qed.
  
Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.


Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl.  destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l.
  induction l.
  simpl.
  intros.
  intros f.
  destruct f.
  simpl.
  destruct (eqbP n x).
  intros.
  simpl in H0.
  discriminate H0.
  intros.
  intros f.
  destruct f.
  apply H.
  symmetry.
  exact H1.
  apply IHl.
  apply H0.
  apply H1.
  
 Qed.
  
Inductive nostutter {X:Type} : list X -> Prop :=
| emptylist: nostutter []
| single x:  nostutter [x]
| diff x y l (H:nostutter (y::l)) (K: x<>y) : nostutter (x::y::l).

Inductive merge {X:Type} : list X -> list X -> list X -> Prop:=
| doubleempty: merge [] [] []
| left x y z l(H:merge y z l) : merge (x::y) z (x::l)
| right x y z l ( H:merge y z l): merge y (x::z) (x::l).

Theorem add_in_front_same: forall X (x:X) l1 l2, l1=l2-> x::l1=x::l2.
intros.
rewrite H.
reflexivity.
Qed.
Theorem filtertest: 
forall (X:Type) l l1 l2 (test: X->bool), merge l1 l2 l-> forallb test l1=true -> 
forallb  (fun x => negb (test x)) l2 = true -> filter test l =l1.
intros.
induction H.
reflexivity.
simpl.
simpl in H0.
destruct (test x) eqn:K.
apply add_in_front_same.
apply IHmerge.
apply H0.
apply H1.
discriminate H0.
simpl.
destruct (test x) eqn:k.
simpl in H1.
rewrite k in H1.
simpl in H1.
discriminate H1.
apply IHmerge.
apply H0.
simpl in H1.
rewrite k in H1.
simpl in H1.
exact H1.
Qed.

