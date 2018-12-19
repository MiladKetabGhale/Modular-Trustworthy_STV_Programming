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
(*Require Import Coq.Program.Basics.
Require Import Coq.Arith.Wf_nat.
Require Import Program.
Require Import  Recdef.
*)

Module Type Params. 

Close Scope Q_scope.


Parameter st : nat. 
Parameter quota : Q.
Parameter cand : Type.
Parameter ValidBallot : list cand -> bool.

Parameter cand_all: list cand.
Parameter cand_nodup: NoDup cand_all.
Parameter cand_finite: forall c, In c cand_all.
Parameter cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.
Parameter cand_in_dec: forall c : cand, forall l : list cand, {In c l} + {~In c l}.


End Params.

(*
Inductive Cand := A | B.

Module Instantiation.

Definition cand := Cand.

Definition cand_all := [A;B].

Lemma cand_nodup : NoDup cand_all.
Proof.
 unfold cand_all.
 apply NoDup_cons.
 intro i.
 inversion i.
 inversion H.
 inversion H.
 apply NoDup_cons.
 intro i.
 inversion i.
 apply NoDup_nil.
Defined.

Lemma cand_finite : forall c, In c cand_all.
Proof.
 intros c.
 destruct c.
 left. auto.
 right. left. auto.
Defined.

Lemma cand_eq_dec : forall (c: cand) d, {c = d} + {c <> d}.
Proof.
 intros.
 destruct c. 
 destruct d.
 left. auto.
 right. intro i. inversion i.
 destruct d.
 right. intro i. inversion i.
 left.
 auto.
Defined.

Lemma cand_in_dec : forall (c: cand) l, {In c l} + {~ In c l}.
Proof.
 intros.
 induction l.
 right.
 intro i.
 inversion i.
 destruct (cand_eq_dec a c) as [ p |q].
 left.
 left. auto.
 destruct IHl as [i | j].
 left. right. auto.
 right.
 intro k.
 apply j.
 destruct k as [k1 | k2].
 contradict q.
 auto.
 auto.
Defined.

Definition st := (1)%nat.

Definition quota := (2 # 1)%Q.

End Instantiation.
*)
(*
Module QTest (X: Params).

Definition cand := (X.cand)%type.

Definition cand_all := X.cand_all.

Definition cand_finite := X.cand_finite.

Definition cand_eq_dec := X.cand_eq_dec.

Definition cand_in_dec := X.cand_in_dec.

Definition st := (X.st)%nat.

Definition quota := X.quota.

End QTest.

Module M := QTest Instantiation.

*)
