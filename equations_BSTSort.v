From Coq Require Import List Arith PeanoNat.
From Equations Require Import Equations.

Import ListNotations.

Inductive nattree : Type :=
| E
| T (l : nattree) (v : nat) (r : nattree).

Definition empty_tree : nattree :=
  E.
  
Fixpoint bound (v : nat) (t : nattree) :=
  match t with
  | E => false
  | T l k r => if v <? k then bound v l
                else if k <? v then bound v r
                     else true
  end.
  
Fixpoint lookup (d v : nat) (t : nattree) : nat :=
  match t with
  | E => d
  | T l k r => if v <? k then lookup d v l
                else if k <? v then lookup d v r
                     else k
  end.
  
Fixpoint insert (v : nat) (t : nattree) : nattree :=
  match t with
  | E => T E v E
  | T l k r => if v <? k then T (insert v l) k r
                 else if k <? v then T l k (insert v r)
                      else T l k r
  end.
  
Fixpoint ForallT (P: nat -> Prop) (t : nattree) : Prop :=
  match t with
  | E => True
  | T l k r => P k /\ ForallT P l /\ ForallT P r
  end.
  
Inductive BST : nattree -> Prop :=
| BST_E : BST E
| BST_T : forall l v r,
    ForallT (fun y => y < v) l ->
    ForallT (fun y => y > v) r ->
    BST l ->
    BST r ->
    BST (T l v r).

Equations fromList (l : list nat) : nattree :=
  fromList [] := empty_tree ;
  fromList (x :: xs) := insert x (fromList xs).
  
Compute (fromList [1;7;4;9;2]).

Equations fromBST (b : nattree) : list nat :=
  fromBST E := [] ;
  fromBST (T l k r) := (fromBST l) ++ (k :: (fromBST r)).
  
Compute (fromBST(fromList [1;7;4;9;2])).

Equations BSTSort (l : list nat) : list nat :=
  BSTSort xs := fromBST (fromList xs).
  
Compute (BSTSort [66;5;4;3;2;1]).

Lemma ForallT_insert : forall (P : nat -> Prop) (t : nattree),
    ForallT P t -> forall (v : nat),
      P v -> ForallT P (insert v t).
Proof.
intros. induction t; simpl.
- auto.
- elim (v <? v0); simpl.
  + intuition.
  + elim (v0 <? v).
    * simpl. simpl in H. intuition.
    * exact H.
Qed.

Theorem insert_BST : forall (v : nat) (t : nattree),
    BST t -> BST (insert v t).
Proof.
induction t.
- intros. simpl. constructor; simpl; intuition.
- intros. simpl in *. destruct (v <? v0) eqn:E.
  + constructor; inversion H; intuition.
    * apply ForallT_insert. exact H3.
      apply Nat.ltb_lt. exact E.
  + destruct (v0 <? v) eqn:E'; inversion H; intuition.
    * constructor; inversion H; intuition.
      -- apply ForallT_insert. exact H13.
         apply Nat.ltb_lt. exact E'.
Qed.


Theorem fromList_BST (l : list nat) : BST (fromList l).
Proof.
funelim (fromList l).
- constructor.
- apply insert_BST. exact H.
Qed.

Inductive Sorted : list nat -> Prop :=
  | Sorted_nil : Sorted nil
  | Sorted_cons {x xs} : Sorted xs -> x <= hd x xs -> Sorted (x :: xs).
  
Search Forall.
Print Forall.

Theorem sorted_treeapp (v : nat) (l r : list nat) :
  Sorted l -> Sorted r -> Forall (fun y => y < v) l -> Forall (fun y => v < y) r -> Sorted (l ++ (v :: r)).
Proof.
revert v r.
induction l.
- simpl. intros. constructor.
  + exact H0.
  + inversion H2.
    * now simpl.
    * simpl. now apply Nat.lt_le_incl.
- simpl. intros. constructor. apply IHl.
  + now inversion H.
  + exact H0.
  + now inversion H1.
  + exact H2.
  + inversion H. inversion H1. destruct l.
    * simpl. now apply Nat.lt_le_incl.
    * simpl. simpl in H6. exact H6.
Qed.

Theorem fromBST_bound_In (t : nattree) (n : nat) : (bound n t = true) -> In n (fromBST t).
Proof.
revert n. induction t.
- intros. exfalso. simpl in H. discriminate.
- intros. simp fromBST. simpl in H. Search (In). apply in_or_app. destruct (n <? v) eqn:E.
  + left. apply IHt1. exact H.
  + right. destruct (v <? n) eqn:E'.
    * Search In. apply in_cons. apply IHt2. exact H.
    * Search In. replace v with n. apply in_eq. Search lt eq. elim (Nat.lt_trichotomy n v).
      -- intros. exfalso. assert (n >= v).
      { Search Nat.ltb. apply Nat.ltb_ge. exact E. }
      apply (le_not_lt v n H1). exact H0.
      -- intros. elim H0.
          ++ easy.
          ++ intros. exfalso. apply (Nat.ltb_nlt v n).
             exact E'. exact H1.
Qed.

Lemma nltb_antisym (n m : nat) :
  (n <? m = false) -> (m <? n = false) -> n = m.
Proof.
elim (Nat.lt_trichotomy n m).
- intros. exfalso. Search Nat.ltb. now apply (Nat.ltb_nlt n m).
- intros. elim H.
  + easy.
  + intros. exfalso. now apply (Nat.ltb_nlt m n).
Qed.

Theorem bound_forall (n : nat) (p : nat -> Prop) (t : nattree) :
  bound n t = true -> ForallT p t -> p n.
Proof.
revert n p. induction t.
- intros. exfalso. simpl in H. discriminate.
- intros. simpl in H. destruct (n <? v) eqn:E.
  + simpl in H0. apply IHt1. exact H. easy.
  + destruct (v <? n) eqn:E'.
    * apply IHt2. exact H. simpl in H0. easy.
    * simpl in H0. replace n with v. easy.
      now apply nltb_antisym.
Qed.

Lemma forall_app (l1 l2 : list nat) (p : nat -> Prop) :
  Forall p l1 -> Forall p l2 -> Forall p (l1 ++ l2).
Proof.
revert p l2. induction l1.
- intros. simpl. exact H0.
- intros. simpl. constructor. inversion H. exact H3. apply IHl1.
  inversion H. exact H4. exact H0.
Qed. 


Lemma forallt_forall (p : nat -> Prop) (t : nattree) :
  ForallT p t -> Forall p (fromBST t).
Proof.
revert p. induction t.
- intros. simp fromBST. constructor.
- intros. simp fromBST. simpl in *. apply forall_app.
  + apply IHt1. easy.
  + constructor. easy. apply IHt2. easy.
Qed.

Theorem fromBST_In_bound (t : nattree) (n : nat) :
  BST t -> In n (fromBST t) -> (bound n t = true).
Proof.
intro b. revert n. induction b.
- intros. exfalso. simp fromBST in H. inversion H.
- intros. simpl in *. simp fromBST in H1. destruct (n <? v) eqn:E.
  + apply IHb1. elim (in_app_or (fromBST l) (v :: fromBST r) n).
    * easy.
    * intros. inversion H2.
      -- exfalso. remember ((proj1 (Nat.ltb_lt n v)) E).
         apply (Nat.lt_neq n v). exact l0. symmetry. exact H3.
      -- exfalso. assert (Forall (fun y => y > v) (fromBST r)).
         { apply forallt_forall. exact H0. }
         Search Forall. remember (proj1 (Forall_forall _ _) H4). assert (n > v). apply g. exact H3. Search Nat.ltb. remember (proj1 (Nat.ltb_lt n v) E). Search lt not. remember (Nat.lt_asymm n v l0). contradiction.
    * exact H1.
  + destruct (v <? n) eqn:E'.
    * apply IHb2. elim (in_app_or (fromBST l) (v :: fromBST r) n).
      -- intros. exfalso.
         assert (Forall (fun y => y < v) (fromBST l)).
         { apply forallt_forall. exact H. }
         remember (proj1 (Forall_forall _ _) H3).
         assert (n < v).
         { apply l0. exact H2. }
         Search Nat.ltb. apply (Nat.ltb_nlt n v). exact E. exact H4.
      -- intros. inversion H2.
         ++ exfalso. Search Nat.ltb. rewrite H3 in E'. remember (Nat.ltb_irrefl n). rewrite e in E'. discriminate.
         ++ exact H3.
      -- exact H1.
    * reflexivity.
Qed.

Theorem fromBST_sorted (t : nattree) : BST t -> Sorted (fromBST t).
Proof.
funelim (fromBST t).
- intros. constructor.
- intros. apply sorted_treeapp.
  + apply H. now inversion H1.
  + apply H0. now inversion H1.
  + inversion H1. apply forallt_forall. exact H5.
  + apply forallt_forall. inversion H1. exact H6.
Qed.

Theorem BSTSort_sorted (l : list nat) : Sorted (BSTSort l).
Proof.
funelim (BSTSort l).
apply fromBST_sorted. apply fromList_BST.
Qed.

Equations NDecList (n : nat) : list nat :=
  NDecList 0 := [] ;
  NDecList (S n) := (S n) :: (NDecList n).
  
Compute (NDecList 5).
Time Compute (BSTSort (NDecList 100)).

Equations? NIncList (l h : nat) : list nat by wf ((S h) - l) :=
  NIncList l h with (h <=? l) :=
    NIncList l h (true) => [] ;
    NIncList l h (false) => l :: (NIncList (S l) h).
Proof.
Abort.

