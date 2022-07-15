Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
From Coq Require Import Unicode.Utf8.


Module AExp.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: ∀ a,
  aeval (optimize_0plus a) = aeval a.
Proof.
    induction a.
    reflexivity.
    simpl. 
    destruct a1 eqn:E.
    induction n.
    rewrite IHa2. reflexivity.
    simpl. rewrite IHa2. reflexivity.
    simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp := 
    match b with 
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

Theorem optimize_0plus_b_sound : ∀ b,
  beval (optimize_0plus_b b) = beval b.
Proof.
    intros b. induction b; try (simpl; reflexivity); 
    try (simpl; 
    rewrite (optimize_0plus_sound a1); rewrite (optimize_0plus_sound a2);
    reflexivity);
    try (simpl; rewrite IHb; reflexivity).
    simpl. rewrite IHb1. rewrite IHb2. reflexivity. 
    Qed.


Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

  Example silly_presburger_example : ∀ m n o p,
  m + n ≤ n + o ∧ o + 3 = p + 3 →
  m ≤ p.
Proof.
  intros. lia.
Qed.
Example add_comm__lia : ∀ m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.
Example add_assoc__lia : ∀ m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.



Module aevalR_first_try.
Inductive aevalR : aexp → nat → Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 →
      aevalR e2 n2 →
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 →
      aevalR e2 n2 →
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 →
      aevalR e2 n2 →
      aevalR (AMult e1 e2) (n1 * n2).


Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.
End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aevalR : aexp → nat → Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) → (e2 ==> n2) → (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) → (e2 ==> n2) → (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) → (e2 ==> n2) → (AMult e1 e2) ==> (n1 *n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : ∀ a n,
  (a ==> n) ↔ aeval a = n.
  Proof.
    split.
    intros.
    induction H.
    reflexivity.
    simpl.
    rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    simpl.
    rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    simpl.
    rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    intros.
    generalize dependent n.
    induction a; simpl;intros; subst.
    apply E_ANum.
    apply E_APlus. apply IHa1. reflexivity. apply IHa2. reflexivity.
    apply E_AMinus. apply IHa1. reflexivity. apply IHa2. reflexivity.
    apply E_AMult.  apply IHa1. reflexivity. apply IHa2. reflexivity.
Qed.
End AExp.

Module aevalR_division.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).
Inductive aevalR : aexp → nat → Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) : (* <----- NEW *)
      (a1 ==> n1) → (a2 ==> n2) → (n2 > 0) →
      (mult n2 n3 = n1) → (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_division.
Module aevalR_extended.

Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aexp : Type :=
  | AAny (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive aevalR : aexp → nat → Prop :=
  | E_Any (n : nat) :
      AAny ==> n (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.
End aevalR_extended.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.


Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.
Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.


Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com → state → state → Prop :=
  | E_Skip : ∀ st,
      st =[ skip ]=> st
  | E_Asgn : ∀ st a n x,
      aeval st a = n →
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : ∀ c1 c2 st st' st'',
      st =[ c1 ]=> st' →
      st' =[ c2 ]=> st'' →
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true →
      st =[ c1 ]=> st' →
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false →
      st =[ c2 ]=> st' →
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      st =[ while b do c end ]=> st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true →
      st =[ c ]=> st' →
      st' =[ while b do c end ]=> st'' →
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').


Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
    apply E_Seq with  (X !-> 0).
    apply E_Asgn.
    simpl. reflexivity.
    apply E_Seq with  (Y !->1;X !-> 0).
    apply E_Asgn.
    simpl. reflexivity.
    apply E_Asgn.
    simpl. reflexivity.
Qed.

Theorem ceval_deterministic: ∀ c st st1 st2,
     st =[ c ]=> st1 →
     st =[ c ]=> st2 →
     st1 = st2.
    Proof.
        intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
  rewrite <- (IHE1_1 st'0 H1) in *.
  apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.
Qed.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Theorem loop_never_stops : ∀ st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.
induction contra; (try discriminate).
inversion Heqloopdef. subst. discriminate.

inversion Heqloopdef. subst. apply IHcontra2. reflexivity.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }> =>
      false
  end.


Inductive no_Whiles : com -> Prop :=
	| noWhilesSKIP : no_Whiles <{skip}>
	| noWhilesAss : forall a1 a2, no_Whiles <{a1 := a2}>
	|noWhilesSeq : forall (a1 a2 : com), no_Whiles a1 -> no_Whiles a2 -> no_Whiles <{a1 ; a2}>
	|noWhilesIf : forall (b : bexp) (a1 a2 : com),
										no_Whiles a1 -> no_Whiles a2 ->
												no_Whiles <{if b then a1 else a2 end }>.

Theorem no_whiles_eqv:
	forall c, no_whiles c = true <-> no_Whiles c.
Proof.
    induction c; simpl; split; intros; try reflexivity; try constructor;
    try destruct IHc1; try destruct IHc2;
    try (apply andb_true_iff in H;
    destruct H; auto). 
    apply andb_true_iff .
    split.
    apply H1.
    inversion H.
    assumption.
    apply H3.
    inversion H.
    assumption.
    apply andb_true_iff.
    split.
    apply H1.
    inversion H.
    assumption.
    apply H3.
    inversion H.
    assumption.
    discriminate.
    inversion H.
    Qed.

Theorem no_whiles_terminating:
  forall c, no_Whiles c -> forall st, exists st', (st =[ c ]=> st').
  Proof.
    intros c H.
    induction H; intros.
    exists st. constructor.
    exists (a1 !-> (aeval st a2); st).
    constructor. reflexivity.
    assert (∃ st' : state, st =[ a1 ]=> st') as terminates_fst.
    apply IHno_Whiles1.
    destruct terminates_fst.
    assert (∃ st' : state, x =[ a2 ]=> st') as terminates_snd.
    apply IHno_Whiles2.
    destruct terminates_snd.
    exists x0.
    apply E_Seq with x; assumption.
    destruct (beval st b) eqn:E.
    assert (∃ st' : state, st =[ a1 ]=> st') as terminates_fst.
    apply IHno_Whiles1.
    destruct terminates_fst.
    exists x.
    apply E_IfTrue; assumption.
    assert (∃ st' : state, st =[ a2 ]=> st') as terminates_fst.
    apply IHno_Whiles2.
    destruct terminates_fst.
    exists x.
    apply E_IfFalse; assumption.
    Qed.






