From LF Require Export Poly.
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. Qed.
  
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.
  
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Lemma list_append_nil: forall X (a:list X), a ++  [ ] = a.
intros X.
induction a.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.
Lemma list_assoc: forall X (a b c:list X), a++b++c = (a++b)++c.
intros X a b c.
induction a.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.
Lemma lemma0: forall X (a b:list X),rev (a ++ b) = rev b ++ rev a.
intros X a b.
induction a.
rewrite list_append_nil.
simpl.
reflexivity.
simpl.
rewrite IHa.
rewrite list_assoc.
reflexivity.
Qed.



Lemma lemma1: forall X (l': list X), l' = rev (rev  l').
intros X l'.
induction l'.
reflexivity.
simpl.
rewrite lemma0.
rewrite <- IHl'.
reflexivity.
Qed.


Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  induction l' as [|h t IH].
  rewrite H.
  rewrite <- lemma1.
  reflexivity.
  rewrite H.
  rewrite <- lemma1.
  reflexivity.
  Qed.
Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.
  
  
Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.
  
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.


Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
  Qed.
  
Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = y :: l ->
  x = z.
Proof.
intros.
injection H.
intros.
apply H2.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
  
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.
  
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  discriminate H.
  Qed.
  
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
   destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.
  

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.
  

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)
  intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *)
    discriminate eq.
    + (* m = S m' *)
      apply f_equal.
   apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.
   
   
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  destruct m.
  reflexivity.
  discriminate.
  induction m.
  discriminate.
  intros H.
  simpl in H.
  apply IHn in H.
  rewrite H.
  reflexivity.
  Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n.
  destruct m eqn:H.
  reflexivity.
  discriminate.
  induction m.
  discriminate.
  simpl.
  intros H.
  rewrite <- plus_n_Sm, <- plus_n_Sm in H.
  injection  H as H'.
  apply IHn in H'.
  rewrite H'.
  reflexivity.
  Qed.
  
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
intros .
generalize dependent n.
induction l.
destruct n eqn:H.
simpl.
reflexivity.
discriminate.
induction n.
simpl.
discriminate.
simpl.
intros.
injection H as H'.
apply IHl.
apply H'.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
Theorem tail_eq: forall (X: Type) (h: X) (l1 l2: list X),
    l1 = l2 -> h :: l1 = h :: l2.
Proof.
  intros. apply f_equal. apply H.
Qed.
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros .
  generalize dependent l1 .
  generalize dependent l2.
  induction l.
  intros.
  injection H as H'.
  rewrite <- H', <- H.
  reflexivity.
  intros.
  simpl in H.
  destruct x.
  destruct (split l).
  injection H as H'.
  rewrite <- H', <- H.
  simpl. apply tail_eq. apply IHl. reflexivity.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros .
  destruct b eqn:H.
  destruct (f true) eqn:H'.
  rewrite H', H'.
  reflexivity.
  destruct (f false) eqn:H''.
  rewrite H'.
  reflexivity.
  rewrite H''.
  reflexivity.
  destruct (f false) eqn:H'.
  destruct (f true) eqn:H''.
  rewrite H''. reflexivity.
  apply H'.
  rewrite H'. apply H'. Qed.
  
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
intros n.
induction n.
induction m.
reflexivity.
reflexivity.
induction m.
reflexivity.
simpl.
apply IHn.
Qed.
Lemma zero_list: forall X (l:list X), length l = 0 -> l = [].
Proof.
intros.
induction l.
reflexivity.
simpl in H.
discriminate H.
Qed.

Definition split_combine_statement : Prop :=
 forall (X: Type) (l1 l2: list X),
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).
  Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros.
  generalize dependent l2.
  induction l1.
  intros.
  assert (l2 =[]).
  induction l2.
  reflexivity.
  discriminate.
  rewrite H0.
  reflexivity.
  intros.
  destruct l2.
  apply zero_list in H.
  rewrite H.
  reflexivity.
  simpl.
  destruct (split (combine l1 l2)) eqn:H'.
  simpl in H'.
  assert( length l1 = length l2).
  simpl in H.
  injection  H.
  intros.
  exact H0.
  apply IHl1 in H0.
  rewrite H' in H0.
  injection H0.
  intros.
  rewrite H1, H2.
  reflexivity.
  Qed.
  
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
 intros.
 generalize dependent test.
 generalize dependent x.
 generalize dependent lf.
 induction l.
 intros.
 simpl in H.
 discriminate H.
 intros.
 simpl in H.
 destruct (test x) eqn:H'.
 injection H.
 intros.
 rewrite <-H1.
 exact H'.
 apply IHl in H.
 exact H.
 Qed.
 
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool:=
match l with
| [] => true
| h::t => if test h then (forallb  test t) else false
end.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool:=
match l with
| [] => false
| h::t => if test h then true else existsb test t
end.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool:=
negb (forallb (fun t => negb(test t)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
  
Proof.
intros.
generalize dependent test.
induction l.
intros.
reflexivity.
intros.
simpl.
destruct (test x) eqn:H.
unfold existsb'.
simpl.
rewrite H.
reflexivity.
unfold existsb'.
simpl. rewrite H.
simpl.
unfold existsb' in IHl.
apply IHl.
Qed.
