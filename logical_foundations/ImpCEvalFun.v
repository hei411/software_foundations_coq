From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp Maps.
From Coq Require Import Unicode.Utf8.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st (* bogus *)
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | <{ skip }> =>
          st
      | <{ l := a1 }> =>
          (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Theorem ceval_step__ceval: ∀ c st st',
      (∃ i, ceval_step st c i = Some st') →
      st =[ c ]=> st'.
    Proof. 
        intros.
        destruct H as [i H].
        generalize dependent c.
        generalize dependent st.
        generalize dependent st'.
        induction i.
        intros.
        inversion H.
        intros.
        induction c; try (inversion H; subst); try reflexivity.
        constructor.
        constructor. reflexivity.
        inversion H.
        destruct (ceval_step st c1 i) eqn:K in H1.
        apply E_Seq with s; (apply IHi ;assumption).
        discriminate.
        destruct (beval st b) eqn:E.
        apply E_IfTrue; auto.
        apply E_IfFalse; auto.
        destruct (beval st b) eqn:E.
        destruct (ceval_step st c i) eqn:F.
        apply E_WhileTrue with s; auto .
        discriminate.
        inversion H1.
        subst.
        apply (E_WhileFalse); auto.
        Qed.

Theorem ceval_step_more: ∀ i1 i2 st st' c,
  i1 ≤ i2 →
  ceval_step st c i1 = Some st' →
  ceval_step st c i2 = Some st'.
  Proof.
    intros i1.
    induction i1; intros i2 st st' c Hle Hceval.
    simpl in Hceval.
    inversion Hceval.
    destruct i2; inversion Hle.
    subst. assumption.
    subst.
    assert (Hle': i1 ≤ i2) by lia.
    destruct c; auto.
    simpl.
    simpl in Hceval.
    destruct (ceval_step st c1 i1) eqn:Heqst1'o.
    apply (IHi1 i2) in Heqst1'o; try assumption.
    rewrite Heqst1'o. apply IHi1; assumption.
    inversion Hceval.
    simpl.
    destruct (beval st b) eqn:B.
    inversion Hceval.
    rewrite B in *. rewrite H1.
    apply (IHi1  i2); assumption.
    inversion Hceval.
    rewrite B in *.
    rewrite H1.
    apply (IHi1 i2); assumption.
    simpl.
    destruct (beval st b) eqn:E; try assumption.
    destruct (ceval_step st c i1) eqn:F.
    apply (IHi1 i2) in F as K; try assumption.
    rewrite K.
    simpl.
    simpl in Hceval.
    rewrite E in Hceval.
    rewrite F in Hceval.
    apply (IHi1 i2) in Hceval; try assumption.
    simpl in Hceval.
    rewrite E in Hceval.
    rewrite F in Hceval. inversion Hceval.
    simpl in Hceval.
    rewrite E in Hceval.
    assumption.
    Qed.

Theorem ceval__ceval_step: ∀ c st st',
      st =[ c ]=> st' →
      ∃ i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce; try (exists 1; reflexivity).
  exists (S 0).
  simpl.
  rewrite H. reflexivity.
  destruct IHHce1.
  destruct IHHce2.
  exists (S(x +x0)).
  simpl.
  rewrite (ceval_step_more x (x+x0) st st' c1).
  rewrite (ceval_step_more x0 (x+x0) st' st'' c2). reflexivity. lia. assumption. lia. assumption.
  destruct IHHce.
  exists (S(x)).
  simpl. rewrite H in *. assumption.
  destruct IHHce.
  exists (S(x)).
  simpl. rewrite H in *. assumption.
  exists (1).
  simpl.
  rewrite H.
  reflexivity.
  destruct IHHce1.
  destruct IHHce2.
  exists (S(x+x0)).
  simpl.
  rewrite H. 
  assert(T:ceval_step st c (x + x0)= Some st').
  apply (ceval_step_more x (x+x0) st st' c).
  lia.
  assumption.
  rewrite T.
  apply (ceval_step_more x0 (x+x0) st' st'' <{ while b do c end }> ).
  lia.
  assumption.
  Qed.
  



Theorem ceval_and_ceval_step_coincide: ∀ c st st',
      st =[ c ]=> st'
  ↔ ∃ i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

    


        
Theorem ceval_deterministic' : ∀ c st st1 st2,
     st =[ c ]=> st1 →
     st =[ c ]=> st2 →
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia. Qed.


        
        
        
