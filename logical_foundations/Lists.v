From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
  
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
  
Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.
  
Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.
  
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
  
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros p.
destruct p as [m n].
reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
  
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
  
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
  
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
  
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil =>  default
  | h :: t =>  h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil =>  nil
  | h :: t =>  t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h::t => match h with 
            |O => nonzeros t
            |k => k::(nonzeros t)
            end
  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h::t => if even h then oddmembers t else h::(oddmembers t)
  end.
  
Definition countoddmembers (l:natlist) : nat:=
length l - length (oddmembers l).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1 with 
|nil => l2
|h::t =>
  match l2 with
  |nil => h::t
  |h'::t'=> h::h'::alternate t t'
  end
end.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
match s with 
|nil => O
|h::t => if eqb h v then 1+count v t else count v t
end.

Definition sum : bag -> bag -> bag :=
app.
Definition add (v : nat) (s : bag) : bag :=
v::s.

Definition member (v : nat) (s : bag) : bool :=
O <? (count v s) .

Lemma n_eq: forall v, v =? v = true.
Proof. induction v. reflexivity.
simpl. rewrite IHv. reflexivity.
Qed.
Theorem bag_theorem: forall v l, count v (add v l) = S (count v l).
intros v l.
induction l as [|h t].
simpl. 
induction v.
reflexivity.
simpl. rewrite IHv. reflexivity.
simpl. induction v.
simpl. reflexivity.
simpl. rewrite n_eq. reflexivity. Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.
    
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.
    
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
  
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite  IHl1'. reflexivity. Qed.
    
Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  induction l as [|h t IHl].
  reflexivity.
  simpl.
  rewrite IHl. reflexivity. Qed.
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [|h t IHl].
  induction l2 as [|h' t' IHl'].
  reflexivity.
  simpl.
  rewrite app_nil_r.
  reflexivity.
  induction l2 as [|h' t' IHl'].
  simpl. rewrite app_nil_r. reflexivity.
  simpl.
  rewrite IHl. simpl. rewrite app_assoc. reflexivity.
  Qed.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [|h t IHl].
  reflexivity.
  simpl. rewrite rev_app_distr. simpl. rewrite IHl. reflexivity. Qed.
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc, app_assoc. reflexivity. Qed.

Lemma non_zeros_con: forall h t, nonzeros(h::t) = nonzeros([h]) ++ nonzeros t.
induction t.
simpl. rewrite app_nil_r. reflexivity.
induction h.
simpl. reflexivity.
simpl. reflexivity.
Qed.
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  induction l1 as [|h t IHl].
  simpl. reflexivity.
  induction l2 as [|h' t' IHl'].
  simpl. rewrite app_nil_r, app_nil_r. reflexivity.
  rewrite non_zeros_con. 
  destruct h eqn:H. 
  simpl. rewrite IHl. simpl. reflexivity.
  simpl. rewrite IHl. simpl. reflexivity.
  Qed.
  
Fixpoint eqblist (l1 l2 : natlist) : bool :=
match l1, l2 with
| nil, nil => true
| h::t, nil=> false
| nil, h::t => false
| h::t, h'::t'=> if h =? h' then eqblist t t' else false
end.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
induction l.
reflexivity.
simpl.
rewrite n_eq. rewrite IHl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
induction s.
reflexivity.
reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
match s with
|nil=> nil
|h::t => if h =? v then t else h:: (remove_one v t)
end.
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  induction s.
  reflexivity.
  simpl.
  destruct n eqn:H.
  simpl. rewrite leb_n_Sn.
  reflexivity.
  simpl. exact IHs. Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  assert(rev (rev l1 ) = rev (rev l2)).
  rewrite H.
  reflexivity.
  rewrite <-rev_involutive. rewrite <- H0. rewrite rev_involutive.
  reflexivity.
  Qed.
  
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
  
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
  
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.
  
Definition hd_error (l : natlist) : natoption :=
match l with
|nil => None
|h::t => Some h
end.
End NatList.

Inductive id : Type :=
  | Id (n : nat).
  
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
Export NatList.
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
intros x.
destruct x eqn:H.
induction n.
reflexivity.
simpl. rewrite n_eq. reflexivity.
Qed.

Module PartialMap.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
  
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
  
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  induction v.
  simpl. rewrite eqb_id_refl.
  reflexivity.
  simpl. rewrite eqb_id_refl. reflexivity.
  Qed.
  
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros H.
  induction d.
  simpl. rewrite H. reflexivity.
  simpl. rewrite H. reflexivity.
  Qed.