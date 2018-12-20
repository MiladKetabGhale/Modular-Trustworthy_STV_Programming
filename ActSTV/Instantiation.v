Require Import Coq.Init.Peano.
Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.NatInt.NZMul.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.ZArith.Znat. 
Require Import Coq.QArith.QArith_base.
Require Import  Coq.QArith.QOrderedType.
Require Import QArith_base Equalities Orders OrdersTac.
Require Import Coq.Sorting.Permutation.
Require Import Wf.
Require Import Lexicographic_Product.
Require Import Qreduction.
Require Import Coq.Bool.Bool.
Require Import Inverse_Image. 
Require Import Coq.Bool.Sumbool.
Require Import Coq.Sorting.Mergesort.
Import ListNotations.
(*Add LoadPath "STV".*)
Add LoadPath "/home/users/u5711205/Modular-STVCalculi/".
Require Import Parameters.
Require Import FrameBase.
Import FrameBase.

Inductive Cand := Alice | Bob | Charlie.

Module Instantiate.

Definition cand := Cand.
Definition cand_all := [Alice;Bob;Charlie].
Definition st := (1)%nat.
Definition qu := (8 # 3)%Q.

Lemma cand_nodup : NoDup cand_all.
Proof.
 unfold cand_all.
  repeat 
    apply NoDup_cons || 
    intro ||
    destruct H as [H1 | H] || 
    discriminate || 
    inversion H. 
  apply NoDup_nil.
Defined.
 
Lemma cand_finite : forall c, In c cand_all.
Proof.
unfold cand_all; intro a; repeat induction a 
                                   || (unfold In; tauto).
Defined.

Lemma cand_eq_dec : forall (c: cand) d, {c = d} + {c <> d}.
Proof.
 intros a b;
  repeat induction a; 
    repeat (induction b) || (right; discriminate) ||(left; trivial).
Defined.

Lemma cand_in_dec : forall (c: cand) l, {In c l} + {~ In c l}.
Proof.
 intros.
 induction l.
 right.
 intro i.
 inversion i.
 destruct (cand_eq_dec a c) as [ p |q].
 left;left; auto.
 destruct IHl as [i | j].
 left; right; auto.
 right.
 intro k.
 apply j.
 destruct k as [k1 | k2].
 contradict q.
 auto.
 auto.
Defined.

(*
Definition st := (1)%nat.

Definition quota := (2 # 1)%Q.
*)

Definition filter_function b := 
   if proj1_sig (fst b)  then true else false.

Definition filter ballots 

End Instantiate.

Module M := B Instantiate.
