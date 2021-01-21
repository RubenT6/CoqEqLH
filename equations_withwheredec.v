From Coq Require Import ZArith Lia PeanoNat List.
From Equations Require Import Equations.

Import ListNotations.

Definition test (z : Z) : Z :=
match z with
  | Z0 => Z0
  | Zpos b => Zneg b
  | Zneg b => Zpos b
end.

Equations? range (from to : Z) : list Z by wf (Z.abs_nat (to - from)) lt :=
  range z1 z2 with Utils.dec (Z.ltb z1 z2) :=
    { | left _ => z1 :: (range (z1 + 1) z2) ;
      | right _ => nil }.
Proof.
apply Zabs_nat_lt.
split.
- remember (proj1 (Z.ltb_lt z1 z2) wildcard).
  apply Zle_minus_le_0. apply Zlt_le_succ. exact l.
- apply Z.sub_le_lt_mono. apply Z.le_refl. apply Z.lt_succ_diag_r.
Defined.

Equations? range' (from to : Z) : list Z by wf (Z.abs_nat (to - from)) lt :=
  range' z1 z2 with Utils.dec (Z.leb z1 z2) :=
    { | left _ => z1 :: (range' (z1 + 1) z2) ;
      | right _ => nil }.
Proof.
Search Z.leb. rewrite Z.leb_le in wildcard. Print Z.le.
Abort.

Equations wheretest (n : nat) : nat :=
  wheretest 0 := 0 ;
  wheretest (S m) := s where s : nat := s := (m + m).

Equations? NIncList (l h : nat) : list nat by wf ((S h) - l) :=
  NIncList l h with Utils.dec (l <=? h) :=
    { | right _ => nil ;
      | left _ => l :: (NIncList (S l) h) }.
Proof.
destruct l.
- rewrite Nat.sub_0_r. apply Nat.lt_succ_diag_r.
- rewrite Nat.sub_succ_r. apply lt_pred_n_n. apply Nat.lt_add_lt_sub_r. simpl. rewrite Nat.leb_le in wildcard0.
rewrite Nat.le_succ_l in wildcard0. exact wildcard0.
Defined.

Compute (NIncList 1 4).
 

