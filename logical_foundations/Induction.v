From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat, n+0=n.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.
  
Theorem minus_n_n: forall n, minus n n=0.
Proof.
  intros n.  induction n as [| n' IHn'].
  simpl. reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.
  
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.
  
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  simpl. rewrite add_0_r_firsttry with m. reflexivity.
  simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity. Qed.
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.
  
  
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [|n' IHn'].
  simpl. reflexivity.
  simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity. Qed.
  
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [|n' IHn'].
  simpl. reflexivity.
  rewrite IHn'. simpl. rewrite negb_involutive. reflexivity. Qed.
  
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite  H.
  reflexivity. Qed.
  
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.
  
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc. rewrite add_assoc.
  assert (H:n+m = m+n).
  rewrite add_comm. reflexivity.
  rewrite H. reflexivity. Qed.
  
Theorem mul_n_Sm : forall n m : nat, n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'.
    rewrite -> add_assoc, add_assoc.
    assert (H : m + n' = n' + m). { rewrite -> add_comm. reflexivity. }
    rewrite -> H. reflexivity.
Qed.
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction n as [|n' IHn'].
  assert ( m*0=0).
  induction m as [|m' IHm'].
  reflexivity.
  simpl. rewrite IHm'. reflexivity.
  rewrite H. reflexivity.
  
  simpl. 
  
  rewrite mul_n_Sm. rewrite IHn'.
  reflexivity. Qed.
  
Lemma S_n_double: forall n:nat, S n + S n = S (S (n+n)).
Proof.
  intros n.
  induction n as [|n' IHn'].
  simpl. reflexivity.
  rewrite IHn'.
  simpl.
  rewrite <-plus_n_Sm. rewrite <- plus_n_Sm. reflexivity.
  Qed.
  
Theorem bin_to_nat_pres_incr: forall n:bin, bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n.
  induction n as [|n' IHn'|n'' IHn''].
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite IHn''. rewrite S_n_double. reflexivity.
  Qed.
  

   
Fixpoint nat_to_bin (n: nat) : bin :=
  match n with
    | O => Z
    | S x =>  incr (nat_to_bin x)
  end.
  
Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. reflexivity.
  Qed.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z=> Z
  | B0 k=> match normalize k with
           |Z=> Z
           |k' => B0 k'
           end
  |B1 k=> B1 (normalize k)
  end.

Lemma lemma0: forall n', match normalize n' with
| Z => Z
| B0 n => B0 (B0 n)
| B1 n => B0 (B1 n)
end = normalize match normalize n' with
                | Z => Z
                | B0 n => B0 (B0 n)
                | B1 n => B0 (B1 n)
                end.
Proof.
intros n'.
induction n'.
reflexivity.
simpl. Admitted.

Lemma lemma1:forall n, nat_to_bin (n + n) = normalize (B0 (nat_to_bin n)).
intros n.
induction n as [|n' IHn'].
reflexivity.
simpl. 
Admitted.
Lemma lemma2: forall n, normalize n = normalize (normalize n).
intros n.
induction n as [|n' IHn'|n'' IHn''].
reflexivity.
simpl. 
Admitted.
Lemma lemma3:forall n, incr(nat_to_bin (n + n)) = normalize (B1 (nat_to_bin n)).
Admitted.
Theorem bin_nat_bin :forall n, nat_to_bin( bin_to_nat n) = normalize n.
Proof.
intros n.
  induction n .
 reflexivity.
 simpl.  rewrite lemma1. rewrite IHn. simpl.  rewrite <-lemma2. reflexivity.
 simpl. rewrite lemma3. rewrite IHn.  simpl. rewrite <- lemma2. reflexivity.
 Qed.
 
 