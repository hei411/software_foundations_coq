Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
  induction n.
  reflexivity.
  discriminate H.
  induction m.
  reflexivity.
  assert (forall n m, n+ S m = S (n+m)).
  induction n0.
  reflexivity.
  intros.
  simpl.
  rewrite IHn0.
  reflexivity.
  rewrite H0 in H.
  discriminate H.
  Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.


Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.



Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.
  
  
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR. Qed.
  
Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 \/ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.


Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not : Prop -> Prop.
End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.
  
  
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros .
  unfold not.
  unfold not in H0.
  intros.
  apply H in H1.
  apply H0 in H1.
  destruct H1.
  Qed.
  
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros.
  unfold not.
  intros.
  destruct H.
  apply H0 in H.
  destruct H.
  Qed.
  
Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.



Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
  
Theorem disc : forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.


Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  intros.
  split.
  destruct H.
  left. apply H.
  destruct H.
  right.
  exact H.
  destruct H.
  left.
  exact H.
  destruct H.
  right.
  exact H0.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  left.
  exact H.
  left.
  exact H.
  destruct H0.
  left.
  exact H0.
  right.
  split .
  exact H.
   exact H0.
   Qed.
   
   
From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
intros n.
induction n.
induction m.
split.
left.
reflexivity.
reflexivity.
split.
left.
reflexivity.
reflexivity.
induction m.
split.
right.
reflexivity.
simpl.
assert (forall n, n*0=0).
induction n0.
reflexivity.
simpl.
exact IHn0.
intros.
apply H.
split.
intros.
simpl in H.
discriminate H.
intros. destruct H.
discriminate H.
discriminate H.
Qed.


Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <->(P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.


Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.
Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.
  
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0 as [x E] .
  apply E in H.
  destruct H.
  Qed.
  
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  intros.
  destruct H.
  destruct H.
  left.
  exists x.
  exact H.
  right.
  exists x.
  exact H.
  intros.
 destruct H.
 destruct H.
 exists x.
 left.
 exact H.
 destruct H.
 exists x.
 right.
 exact H.
 Qed.
 Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
  
Theorem In_map :
  forall (A B : Type) (f : A-> B) (l : list A) (x : A),
         In x l->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.


Theorem In_map_iff :
  forall (A B : Type) (f : A-> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  intros. induction l.
  simpl in H.
  destruct H.
  simpl in H. destruct H.
  exists x.
  split.
  apply H.
  simpl.
  left.
  reflexivity.
  apply IHl in H.
  destruct H.
  exists x0.
  split.
  destruct H.
  exact H.
  simpl.
  right.
  destruct H.
  exact H0.
  intros.
  destruct H.
  destruct H.
  induction l.
  simpl in H0.
  destruct H0.
  simpl.
  
  simpl in H0.
  destruct H0.
  left.
  rewrite H0.
  exact H.
  apply IHl in H0.
  right.
  exact H0.
  Qed.
  Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  intros.
  induction l'.
  simpl.
  split.
  intros.
  destruct H.
  intros.
  destruct H.
  destruct H.
  destruct H.
  simpl.
  split.
  intros.
  destruct H.
  right. left. exact H.
  right. right. exact H.
  simpl in IHl'.
  intros.
  destruct H.
  destruct H.
  exact H.
  intros.
  split.
  intros.
  simpl in H.
  destruct H.
  left.
  simpl.
  left.
  exact H.
  rewrite IH in H.
  destruct H.
  left.
  simpl.
  right.
  exact H.
  right.
  exact H.
  intros.
  destruct H.
  simpl.
  simpl in H.
  destruct H.
  left.
  exact H.
  right.
  apply IH.
  left.
  exact H.
  simpl.
  right.
  apply IH.
  right.
  exact H.
  Qed.
  
 Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
 match l with
  |nil => True
  |x :: l => (P x) /\ (All P l)
 end.
 Theorem All_In :
  forall T (P : T-> Prop) (l : list T),
    (forall x, In x l-> P x) <->
    All P l.
Proof.
  intros.
  split.
  intros.
  induction l.
  exact I.
  simpl.
  split.
  simpl in H.
  apply H.
  left.
  reflexivity.
  apply IHl.
  intros.
  apply H.
  simpl.
  right.
  exact H0.
  intros.
  induction l.
  destruct H0.
  destruct H.
  destruct H0.
  rewrite H0 in H.
  exact H.
  apply IHl in H1.
  exact H1.
  exact H0.
  Qed.
  
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].
Lemma append_comm: forall X (x y z: list X), x++y++z = (x++y)++z.
intros X x. 
induction x.
reflexivity.
simpl.
intros.
rewrite IHx.
reflexivity.
Qed.
Lemma con_one : forall X (x:X) y, [x] ++ y = x::y.
intros.
generalize dependent x.
induction y.
reflexivity.
intros.
simpl.
reflexivity.
Qed.
Lemma lemma: forall X (x y:list X) , rev_append x y = (rev_append x []) ++ y.
intros.
generalize dependent y.
induction x.
reflexivity.
intros y.
simpl.
rewrite IHx, IHx with [x].
rewrite <- append_comm.
rewrite con_one.
reflexivity.
Qed.



Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
intros.
apply functional_extensionality.
intros.
induction x.
reflexivity.
simpl.
unfold tr_rev.
simpl.
unfold tr_rev in IHx.
rewrite <- IHx.
rewrite lemma.
reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.


Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
  induction n.
  exists 0.
  reflexivity.
  destruct IHn .
  rewrite even_S.
  destruct (even n).
  exists x.
  simpl.
  rewrite H.
  reflexivity.
  exists (S x).
  rewrite H.
  reflexivity.
  Qed.
  
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
  Proof.
  split.
  destruct (even_double_conv n) as [k Hk].
  intros.
  rewrite H in Hk.
  exists k.
  exact Hk.
  intros [k Hk].
  rewrite Hk.
  apply even_double.
  Qed.  
  
Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. assert (forall n, n=? n = true).
  induction n. reflexivity. simpl. rewrite IHn. reflexivity.
  apply H0.
Qed.


Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros.
  split.
  destruct b1, b2 .
  split.
  reflexivity.
  reflexivity.
  simpl.
  intros.
  destruct H.
  split.
  reflexivity.
  reflexivity.
  simpl.
  intros.
  destruct H.
  split.
  reflexivity.
  reflexivity.
  intros.
  destruct H.
  split.
  reflexivity.
  reflexivity.
  intros.
  destruct H.
  rewrite H, H0.
  reflexivity.
  Qed.
Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros.
  split.
  destruct b1, b2.
  intros.
  left.
  reflexivity.
  left.
  reflexivity.
  right.
  reflexivity.
  intros.
  destruct H.
  right.
  reflexivity.
  intros.
  destruct H.
  rewrite H.
  reflexivity.
  rewrite H.
  destruct b1.
  reflexivity.
  reflexivity.
  Qed.
  
Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
intros.
split.
  intros.
  generalize dependent x.
  induction y.
  induction x.
  intros.
  simpl in H.
  discriminate H.
  intros.
  destruct H.
  induction x.
  unfold not.
  intros.
  discriminate H.
  unfold not.
  intros.
  discriminate H.
  intros x.
  induction x.
  intros.
  unfold not.
  intros.
  discriminate H0.
  intros.
  unfold not.
  intros.
  injection  H0.
  intros.
  simpl in H.
  apply IHy in H.
  unfold not in H.
  apply H in H1.
  apply H1.
  intros.
  unfold not in H.
  generalize dependent y.
   induction x.
   induction y.
   intros.
   destruct H.
   reflexivity.
   intros. 
   reflexivity.
   induction y. intros.
   reflexivity.
   intros.
   simpl.
   apply IHx.
   intros.
   assert (S x = S y).
   rewrite H0.
   reflexivity.
   apply H in H1.
   exact H1.
   Qed.
   
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool:=
match l1, l2 with
| [], [] => true
| _, [] => false
| [], _ => false
| h::t, h'::t' => if eqb h h' then eqb_list eqb t t' else false
end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
    
Proof.
intros.
generalize dependent eqb .
generalize dependent l2 .
induction l1.
intros.
induction l2.
split.
reflexivity.
reflexivity.
split.
discriminate.
simpl.
discriminate.
induction l2.
intros.
split.
discriminate.
discriminate.
intros.
split.
simpl.
destruct (eqb x x0) eqn:K.
intros. apply IHl1 in H0.
rewrite H0. apply H in K.
rewrite K.
reflexivity.
intros. apply H.
discriminate.
simpl . destruct (eqb x x0) eqn:K.
intros. apply IHl1. intros.
apply H.
injection H0.
intros. exact H1.
intros.
injection H0.
intros. apply H in H2.
rewrite K in H2.
discriminate H2.
Qed.
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
intros.
generalize dependent test.
induction l.
intros.
split.
reflexivity.
reflexivity.
intros.
split.
intros.
simpl.
split.
simpl in H.
destruct (test x) eqn:K in H.
exact K.
discriminate H.
simpl in H.
destruct (test x) eqn:K in H.
apply IHl in H.
exact H.
discriminate H.
intros.
simpl.
destruct (test x) eqn:K.
apply IHl.
simpl in H.
destruct H.
exact H0.
simpl in H. destruct H.
rewrite H in K.
discriminate K.
Qed.
Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.  

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~~ (P \/ ~ P).
Proof.
  unfold not. intros P H. 
  apply H.
  right.
  intros. destruct H.
  left.
  apply H0.
  Qed.

Definition excluded_middle := forall P : Prop,
  P \/~ P.
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
intros.
unfold not in H0.
unfold excluded_middle in H.
assert (P x \/ ~ (P x)).
apply H.
destruct H1.
exact H1.
destruct H0.
exists x.
exact H1.
Qed.


Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).
  
Theorem thm1: excluded_middle  -> peirce .
Proof.
intros.
unfold excluded_middle in H.
unfold peirce.
intros.
assert (P \/ ~P).
apply H.
destruct H1.
exact H1.
unfold not in H1.
apply H0.
intros.
apply H1 in H2.
destruct H2.
Qed.


Theorem thm2: peirce  -> double_negation_elimination .
unfold peirce.
unfold double_negation_elimination.
intros.
unfold not in H0.
apply H with (Q:=False).
intros.
apply H0 in H1.
destruct H1.
Qed.


Theorem thm3: double_negation_elimination  -> de_morgan_not_and_not .
Proof.
unfold double_negation_elimination.
unfold de_morgan_not_and_not.
intros.
unfold not in H0.
unfold not in H.



assert (((P \/ Q -> False) -> False) -> P \/ Q).
apply H. 
apply H1.
intros.
assert (forall P Q:Prop,((P -> False) /\ (Q -> False) -> False)->((P \/ Q -> False) -> False)).
intros.
apply H3.
split.
intros.
assert (P0 \/ Q0).
left.
exact H5.
apply H4 in H6.
exact H6.
intros.
assert (P0\/Q0).
right.
exact H5.
apply H4 in H6.
exact H6.
apply H3 in H0.
exact H0.
exact H2.
Qed.


Theorem thm4: de_morgan_not_and_not  -> implies_to_or .
Proof.
unfold de_morgan_not_and_not.
unfold implies_to_or.
intros.
assert(~ (~ ~P /\ ~ Q) -> ~P \/ Q).
apply H.
destruct H1.
unfold not.
intros.
destruct H1.
assert (P->False).
intros.
apply H0 in H3.
apply H2 in H3.
exact H3.
apply H1 in H3.
exact H3.
left.
apply H1.
right.
apply H1.
Qed.


Theorem thm5: implies_to_or  -> excluded_middle .
Proof.
unfold implies_to_or.
unfold excluded_middle.
intros.
assert((P -> P) -> ~ P \/ P).
apply H.
assert (P->P).
intros.
exact H1.
apply H0 in H1.
destruct H1.
right.
exact H1.
left.
exact H1.
Qed.


