From Coq Require Import Arith List Lia Bool Sorting.
From Equations Require Import Equations.

Import ListNotations.

Open Scope list_scope.

(* Inductive natlist : Set := 
| nil : natlist
| cons : nat -> natlist -> natlist. *)

Definition natlist := list nat.

Equations app (n : nat) (l l' : natlist) : natlist :=
  app n nil l' := n :: l' ;
  app n (cons a l) l' := a :: (app n l l').
  
Check app_elim.
  
Global Transparent app.

Print app.

Inductive Sorted : natlist -> Prop :=
  | Sorted_nil : Sorted nil
  | Sorted_cons {x xs} : Sorted xs -> x <= hd x xs -> Sorted (x :: xs).

(* Lemma sorted_split : *)

Lemma filter_length (l : natlist) (f : nat -> bool) :
  length (filter f l) <= length l.
Proof.
induction l; simpl.
- lia.
- destruct (f a); simpl; lia.
Qed.

(** quicksort using filter instead of split
    hopefully this will make further proofs easier
*)
Equations? quicksort (xs : natlist) : natlist 
by wf (length xs) lt :=
  quicksort nil := nil ;
  quicksort (cons y ys) := (quicksort (filter (fun x => x <=? y) ys)) ++ y :: (quicksort (filter (fun x => negb (x <=? y)) ys)).
Proof.
- destruct (filter_length ys (fun x : nat => x <=? y)); lia.
- destruct (filter_length ys (fun x : nat => negb (x <=? y))); lia.
Defined.

Global Transparent quicksort.

Time Compute (quicksort (3::5::3::2::1::nil)).

Extraction Language Haskell.

Recursive Extraction quicksort.

Print quicksort_graph.
Print quicksort_graph_correct.
  
Lemma sorted_easy : Sorted (1::2::nil).
Proof.
constructor.
constructor.
constructor.
now simpl.
simpl.
lia.
Qed.

Lemma in_app (m n : nat) (l l' : natlist) :
  (m = n \/ In m l \/ In m l') -> In m (l ++ n :: l').
Proof.
revert m n l'.
induction l.
- intros. simpl in *.
  elim H.
  + intros. left. symmetry. exact H0.
  + intros.
    elim H0.
    * contradiction.
    * intros. right. exact H1.
- intros. simpl.
  elim H.
  + intros. right. apply IHl. left. exact H0.
  + intros.
    elim H0.
    * intros.
      inversion H1.
      -- left. exact H2.
      -- right. apply IHl. right. left. exact H2.
    * intros. right. apply IHl. repeat right. exact H1.
Qed.

Lemma app_in (m n : nat) (l l' : natlist) :
  In m (l ++ n :: l') -> (m = n \/ In m l \/ In m l').
Proof.
revert m n l'.
induction l.
- intros. simpl in *.
  elim H.
  + intros. left. symmetry. exact H0.
  + intros. repeat right. exact H0.
- intros. simpl in H. elim H.
  + intros. right. left. simpl. left. exact H0.
  + intros. simpl. remember (IHl m n l' H0).
    elim o; intuition.
Qed.

Lemma app_sorted (n : nat) (l l' : natlist) :
  Sorted l -> Sorted l' ->
  forallb (fun x => x <=? n) l = true ->
  forallb (fun x => negb (x <=? n)) l' = true -> Sorted (l ++ n :: l').
Proof.
revert n l'.
induction l.
- intros. simpl. constructor.
  + exact H0.
  + destruct l' eqn:E.
    * simpl. lia.
    * simpl.
      assert (forall x, In x (n0 :: n1) ->
              (fun x : nat => negb (x <=? n)) x = true).
      { apply forallb_forall. exact H2. }
      simpl in *.
      assert (negb (n0 <=? n) = true).
      { apply H3. left. reflexivity. }
      assert (n0 <=? n = false).
      { rewrite negb_intro at 1. rewrite H4. reflexivity. }
      assert (n < n0).
      { apply leb_complete_conv. exact H5. }
      lia.
- intros. simpl. constructor.
  + apply IHl.
    * inversion H. exact H5.
    * exact H0.
    * simpl in H1. rewrite andb_true_iff in H1.
      destruct H1. exact H3.
    * exact H2.
  + destruct l eqn:E.
    * simpl in *. rewrite andb_true_iff in H1.
      destruct H1. apply leb_complete. exact H1.
    * simpl. inversion H. simpl in H6. exact H6.
Qed.

Lemma in_qs (n : nat) (l : natlist) : In n l <-> In n (quicksort l).
Proof.
split.
- revert n.
  funelim (quicksort l).
  + now simpl.
  + intros. apply in_app. inversion H1.
    * now left.
    * right. destruct (n0 <=? n) eqn:E.
      -- left. apply H. now rewrite filter_In.
      -- right. apply H0. rewrite filter_In. split.
         ++ exact H2.
         ++ rewrite E.
            reflexivity.
- revert n.
  funelim (quicksort l).
  + now simpl.
  + intros.
    set (f := (quicksort (filter (fun x : nat => x <=? n) l))).
    set (s := (quicksort (filter (fun x : nat => negb (x <=? n)) l))).
    remember (app_in n0 n f s H1).
    elim o.
    * intros. simpl. now left.
    * intros. elim H2.
      -- intros. simpl.
         assert (In n0 (filter (fun x : nat => x <=? n) l)).
         { apply H. exact H3. }
         right. rewrite filter_In in H4. destruct H4. exact H4.
      -- intros. simpl.
         assert (In n0 (filter (fun x : nat => negb (x <=? n)) l)).
         { apply H0. exact H3. }
         right. rewrite filter_In in H4. destruct H4. exact H4.
Qed.

Check forallb_forall.

Theorem qs_sorted (l : natlist) : Sorted (quicksort l).
Proof.
funelim (quicksort l).
- constructor.
- apply app_sorted.
  + exact H.
  + exact H0.
  + apply forallb_forall.
    induction l.
    * now simpl.
    * simpl.
      destruct (a <=? n) eqn:E.
      -- intros. rewrite <- in_qs in H1. simpl in H1. elim H1.
         ++ intros. now rewrite H2 in E.
         ++ intros. now rewrite filter_In in H2.
      -- intros. rewrite <- in_qs in H1. rewrite filter_In in H1.
         now destruct H1.
  + apply forallb_forall.
    induction l.
    * now simpl.
    * simpl. destruct (a <=? n) eqn:E.
      -- simpl. intros. rewrite <- in_qs in H1.
         rewrite filter_In in H1. now destruct H1.
      -- simpl. intros. rewrite <- in_qs in H1. simpl in H1.
         elim H1.
         ++ intros. rewrite H2 in E. rewrite E. reflexivity.
         ++ intros. rewrite filter_In in H2. now destruct H2.
Qed.

Lemma split_filter_app (n : nat) (l : natlist) :
  Permutation.Permutation l ((filter (fun x : nat => x <=? n) l) ++ (filter (fun x : nat => negb (x <=? n)) l)).
Proof.
revert l n. induction l.
- intros. simpl. constructor.
- intros. destruct (a <=? n) eqn:E.
  + simpl. rewrite E. simpl. constructor. apply IHl.
  + simpl. rewrite E. simpl. apply Permutation.Permutation_cons_app.
    apply IHl.
Qed. 

Theorem qs_permutation (l : natlist) : Permutation.Permutation l (quicksort l).
Proof.
funelim (quicksort l).
- constructor.
- apply Permutation.Permutation_cons_app. 
  apply (Permutation.Permutation_trans (split_filter_app n l)).
  apply Permutation.Permutation_app. exact H. exact H0.
Qed.

Equations NDecList (n : nat) : list nat :=
  NDecList 0 := [] ;
  NDecList (S n) := (S n) :: (NDecList n).
  
Time Compute (quicksort (NDecList 100)).
