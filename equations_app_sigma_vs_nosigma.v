From Coq Require Import Arith List Lia Vector Permutation.
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

Section App.

Set Program Mode.

Equations app {n m} (v : nvector n) (w : nvector m) :
  (Σ k : nat, nvector k) by wf n lt :=
    app []v w := (_,w) ;
    app (cons a v) w := (_,a |:| (app v w).2).

Lemma app_empty : forall (n : nat) (v : nvector n), (app v []v) = (_,v).
Proof.
induction v; simp app.
reflexivity.
rewrite IHv. reflexivity.
Qed.

Equations app' {n m} (v : nvector n) (w : nvector m) :
  nvector (n + m) by wf n lt :=
    app' []v w := w ;
    app' (cons a v) w := a |:| app' v w.

Lemma app'_empty : forall (n : nat) (v : nvector n), (app' v []v) = v.
Proof.
induction v.
simp app'. simpl. unfold eq_rect. Check plus_n_O.
Abort.
(* Seems to require UIP (or similar), earlier definition therefore seems more usable in proofs, although slightly strange *)

Equations? app'' {n m} (v : nvector n) (w : nvector m) :
  (Σ k : nat, { _ : nvector k | k = n + m }) by wf n lt :=
    app'' []v w := (_,w) ;
    app'' (cons a v) w := (_,a |:| (app'' v w).2).
Proof.
apply eq_S.
destruct app''. destruct pr2. simpl. exact e.
Defined.

Check existT.

Lemma app''_empty : forall (n : nat) (v : nvector n),
  app'' v []v = (_,exist _ v _).
Proof.
intros. funelim (app'' v []v).
- simp app''. simpl. unfold eq_rect. reflexivity.
- simp app''. simpl in *. destruct H. Search ((_,_) = (_,_)). dependent rewrite H. inversion H. dependent rewrite H3. inversion_sigma. dependent rewrite H3. dependent rewrite H2. simpl. apply DepElim.pack_sigma_eq. apply DepElim.pack_sigma_eq_nondep. 


