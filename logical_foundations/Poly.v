From LF Require Export Lists.
Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
 end.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
  
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
              
          
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
  
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
match l with
| nil => ([],[])
| (x,y)::tl => (x:: (fst (split tl)), y::(snd(split tl)))
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl. reflexivity.
Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
End OptionPlayground.

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
  
Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).
  
Definition filter_even_gt7 (l : list nat) : list nat :=
filter (fun x => even x && (7 <? x)) l.

Definition partition {X : Type}
                     (test : X-> bool)
                     (l : list X)
                   : list X * list X :=
(filter test l, filter (fun x => negb (test x)) l).

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma lemma1: forall (X Y: Type) (f:X->Y) (l:list X) (x : X) ,
map f (l ++ [x]) = map f (l) ++ [f x].
Proof.
intros X Y.
intros f l x.
induction l as [|h t IHl'].
reflexivity.
simpl. rewrite IHl'. reflexivity. Qed.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y.
  intros f l.
  induction l as [|h t IHl].
  reflexivity.
  simpl.
  rewrite <- IHl.
  rewrite lemma1. reflexivity.
   Qed.
   
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y :=
  match l with
  | nil => nil
  | h::t => app (f h) (flat_map f t)
  end.
               

  Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
  
Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.

Module Exercises.
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [|h t IHl'].
  reflexivity.
  assert (length (h::t) = 1 + length t).
  reflexivity.
  rewrite H.
  rewrite <- IHl'.
  reflexivity.
  Qed.
  
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=

fold  (fun x l => f x :: l) l [].

 
 
 
Theorem fold_map_correct : forall X Y (f: X -> Y)(l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [|h t IHl'].
  reflexivity.
  simpl. 
  unfold fold_map in IHl'.
  unfold fold_map.
  simpl.
  rewrite IHl'. reflexivity.
  
  
  Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y-> Z) (p : X * Y) : Z :=
f (fst p) (snd p).

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
  Qed.
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
  
Proof.
intros X Y Z f p.
destruct p.
reflexivity.
Qed.

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.
Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition succ (n : cnat) : cnat:=
fun (X:Type) (f:X->X) (x:X) => f (n X f x).

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).
  
Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X  (m X f) x.
  
Definition exp (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X->X) (n X)) f x.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.
End Exercises.