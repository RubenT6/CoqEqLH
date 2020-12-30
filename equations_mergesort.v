From Coq Require Import Arith List Lia Vector.
From Equations Require Import Equations.

Notation vector := t.
Notation nvector := (t nat).

Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.

Declare Scope vect_scope.
Notation " x |:| y " := (@Vector.cons _ x _ y) (at level 20, right associativity) : vect_scope.
Notation " x |: n :| y " := (@Vector.cons _ x n y) (at level 20, right associativity) : vect_scope.
Notation "[]v" := Vector.nil (at level 0) : vect_scope.
Local Open Scope vect_scope.

Import Sigma_Notations.

Inductive Sorted : forall {n}, nvector n -> Prop :=
| Sorted_nil : Sorted nil
| Sorted_cons {x n} {xs : nvector n} : Forall (le x) xs -> Sorted xs -> Sorted (x |:| xs).

Lemma sorted_test : Sorted (1 |:| 2 |:| 3 |:| []v).
Proof.
repeat (constructor + lia).
Qed.

Section MergeSort.
Set Program Mode.

(* TODO: make type simpler i.e. nvector (n+m) 
   This actually makes proofs more difficult as we can't separate the vector and the length (including proof of equality of output length and required length)
*)
Equations? merge {n m} (v1 : nvector n) (v2 : nvector m) :
  (Σ (k : nat), { v : nvector k | k = n + m }) by wf (n + m) lt :=
    merge []v xs := (_,xs) ;
    merge xs []v := (_,xs) ;
    merge (x |:| xs) (y |:| ys) with (x <=? y) :=
      { | true => (_,x |:| (merge xs (y |:| ys)).2) ;
        | false => (_,y |:| (merge (x |:| xs) ys).2) }.
Proof.
- apply eq_S.
  destruct merge. destruct pr2.
  simpl. exact e.
- lia.
- simpl. apply eq_S.
  destruct merge. destruct pr2.
  simpl. rewrite <- Nat.add_succ_comm. exact e.
Defined.

(*
Global Transparent merge.

Compute ((merge (1 |:| 4 |:| 7 |:| []v) (4 |:| 2 |:| 6 |:| []v)).2).

Compute (splitat (Nat.div2 5) (1 |:| 2 |:| 3 |:| 4 |:| 5 |:| []v)).
*)

Lemma sorted_le_hd {n} (h : nat) (v : nvector n) :
  Sorted(h |:| v) -> Forall (le h) v.
Proof.
revert h. revert dependent n. induction v.
- intros. constructor.
- intros. constructor.
  + inversion H. dependent rewrite H2 in H3. inversion H3. exact H8.
  + inversion H. dependent rewrite H2 in H3.
    inversion H3. dependent rewrite H7 in H9. exact H9.
Qed.

Lemma le_hd_sorted {n} (h h' : nat) (v : nvector n) :
  h <= h' -> Sorted (h' |:| v) -> Forall (le h) (h' |:| v).
Proof.
revert h h'. revert dependent n. induction v.
- intros. constructor. exact H. constructor.
- intros. constructor.
  + exact H.
  + apply IHv.
    * inversion H0. dependent rewrite H3 in H4. inversion H4. lia.
    * inversion H0. dependent rewrite H3 in H5. exact H5.
Qed.

Lemma in_merge {n m} (x : nat) (vn : nvector n) (vm : nvector m) :
  In x (proj1_sig (merge vn vm).2) -> In x vn \/ In x vm.
Proof.
revert dependent m. revert dependent n. induction vn.
- intros. simp merge in H. right. exact H.
- intros. revert dependent m. induction vm.
  + simp merge. intros. left. exact H.
  + intros. simp merge in H. destruct (h <=? h0).
    * simpl in *. inversion H.
      -- left. constructor.
      -- dependent rewrite H3 in H2.
         assert (In x vn \/ In x (h0 |:| vm)).
         { apply IHvn. exact H2. }
         elim H4.
         ++ intros. left. constructor. exact H5.
         ++ intros. right. exact H5.
    * simpl in *. inversion H.
      -- right. constructor.
      -- dependent rewrite H3 in H2.
         assert (In x (h |:| vn) \/ In x vm).
         { apply IHvm. exact H2. }
         elim H4.
         ++ intros. left. exact H5.
         ++ intros. right. constructor. exact H5.
Qed.

Lemma le_merge {n m} (h : nat) (vn : nvector n) (vm : nvector m) :
  Forall (le h) vn -> Forall (le h) vm ->
    Forall (le h) (proj1_sig (merge vn vm).2).
Proof.
intros. apply Forall_forall.
intros. assert (In a vn \/ In a vm).
{ apply in_merge. exact H1. }
elim H2.
- intros. apply (Forall_forall nat (le h) n vn). exact H. exact H3.
- intros. apply (Forall_forall nat (le h) m vm). exact H0. exact H3.
Qed.

Lemma merge_sorted {n m} (v1 : nvector n) (v2 : nvector m) :
  Sorted v1 -> Sorted v2 -> Sorted (merge v1 v2).2.
Proof.
revert dependent m. revert dependent n. induction v1.
- intros. simpl. exact H0.
- induction v2.
  + intros. simp merge.
  + intros. simp merge. destruct (h <=? h0) eqn:E.
    * simpl. constructor.
      -- apply le_merge. apply sorted_le_hd. exact H.
         apply le_hd_sorted.
         ++ apply leb_complete. exact E.
         ++ exact H0.
      -- apply IHv1. inversion H. 
         dependent rewrite H3 in H5. exact H5.
         exact H0.
    * simpl. constructor.
      -- apply (le_merge h0 (h |:| v1) v2). apply le_hd_sorted.
         rewrite leb_iff_conv in E. lia.
         exact H.
         apply sorted_le_hd. exact H0.
      -- apply IHv2. exact H. inversion H0.
         dependent rewrite H3 in H5. exact H5.
Qed.

Equations? splitinhalf' {n} (v : nvector n) :
  Σ (k1 : nat) (k2 : nat),
    { v' : nvector k1 * nvector k2 | k1 = Nat.div2 n /\ k2 = n - (Nat.div2 n) /\ forall x : nat, In x v <-> In x (fst v') \/ In x (snd v')  }:=
    splitinhalf' xs := (_,_,splitat (Nat.div2 n) xs).
Proof.
- exact (n - Nat.div2 n).
- apply le_plus_minus. induction n.
  + simpl. lia.
  + assert (Nat.div2 (S n) <= n) by (apply Nat.le_div2). lia.
- simpl. split.
  + reflexivity.
  + split.
    * reflexivity.
    * intros. split.
      -- revert x. induction xs.
         ++ intros. exfalso. inversion H.
         ++ intros. inversion H.
            ** destruct n.
Abort.
(* Horrible due to proof terms in last obligation *)

Equations? mergesort {n} (v : nvector n) : nvector n by wf n lt :=
  mergesort nil := nil ;
  mergesort (cons x nil) := cons x nil ;
  mergesort xs := (merge (mergesort (fst (splitat (Nat.div2 n) xs))) (mergesort (snd (splitat (Nat.div2 n) xs)))).2.
Proof.
- exact (S(S n) - (Nat.div2 n)).
- apply le_plus_minus. apply Nat.div2_decr. lia.
- Search (_ < _ -> _ < S _). destruct n. 
  + simpl. lia. 
  + apply Nat.lt_lt_succ_r. apply Nat.lt_lt_succ_r.
    apply Nat.lt_div2. lia.
-
 Abort.
(* not true, we need more information from the splitat function *)

Print splitat.

(* TODO: split v' = v1, v2 and prove app v1 v2 = v *)
Equations? splitinhalf {n} (v : nvector n) :
  Σ (k1 : nat) (k2 : nat),
    { v' : nvector k1 * nvector k2 |
      k1 = Nat.div2 n /\ k2 = n - (Nat.div2 n) } :=
    splitinhalf xs := (_,_,splitat (Nat.div2 n) xs).
Proof.
apply le_plus_minus. apply Nat.div2_decr. lia.
Defined.

Equations? mergesort {n} (v : nvector n) :
  (Σ n : nat, nvector n) by wf n lt :=
  mergesort nil := (_,nil) ;
  mergesort (cons x nil) := (_,cons x nil) ;
  mergesort xs := (_,(merge (mergesort (fst (splitinhalf xs).2.2)).2 (mergesort (snd (splitinhalf xs).2.2)).2).2).
Proof.
- subst xs. destruct splitinhalf. destruct pr2. destruct pr2. simpl. destruct a. rewrite H. apply Nat.lt_div2. lia.
- subst xs. destruct splitinhalf. simpl. destruct pr2. destruct pr2. simpl. destruct a. rewrite H0. Search (_ - _ < _). apply Nat.sub_lt.
  assert (Nat.div2 (S (S n)) < S (S n)).
  { apply Nat.lt_div2. lia. }
  lia. induction n.
  + simpl. lia.
  + simpl. destruct n. lia. lia.
Defined.

(** Issues with pattern-matching using with *)
(*
Equations? mergesortw {n} (v : nvector n) : nvector n by wf n lt :=
  mergesortw nil := nil ;
  mergesortw (cons x nil) := cons x nil ;
  mergesortw xs := let (f,s) := (splitinhalf xs).2.2 in (merge (mergesortw (fst f)) (mergesortw (snd f))).2.
*)

Lemma ms_sorted {n} (v : nvector n) : Sorted (mergesort v).2.
Proof.
funelim (mergesort v).
- constructor.
- simp mergesort. constructor. constructor. constructor.
- simp mergesort. apply merge_sorted. exact H. exact H0.
Qed.


Print eq_sym.

 unfold eq_rect.
Abort.




(** We may need UIP? This would certainly help this proof
    Maybe related to NoConfusion/Subterm etc.?
*)

 Check eq_rect. assert (Sorted (mergesort (h0 |:| t0))). apply (H1 (S n) (h0 |:| t0) (test2 n) (S n) (h0 |:| t0) eq_refl). unfold eq_rect. reflexivity. destruct t0.
  + simp mergesort. funelim (splitinhalf (h |:| h0 |:| []v)). simpl.
  
  
   rewrite <- Heqcall. unfold eq_rect.  unfold mergesort_obligation_3. simpl.


 rewrite <- Heqcall. clear Heqcall. simp mergesort in *. simp merge in *.


