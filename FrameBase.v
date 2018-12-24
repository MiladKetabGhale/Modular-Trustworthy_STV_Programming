(* STV with fractional transfer (ANU Union rules) as instance of generic vote counting. *)
 
(* the first section is the generic part of the formalisation.*)
(*the second section is the specialized part of the formalisation under the section "unionCount", which is formalisation of ANU_Union STV*)

(*In the section unionCount, lines 163-1539 consist of lemmas and functions that we use to prove the two main theorems; measure decrease and rule application*)
(*lines 1540-2590 consist of formalisation of rules of counting for ANU_STV and main theorems.*)
(*the theorem Measure-decrease is separated into lemmas from line 1854 to line 2170*)
(*the theorem Rule application begins from line 2251*)
(*the theorem that is extracted is in line 2561*)

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
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Wf_nat.
Require Import Program.
Require Import  Recdef.
Add LoadPath "/home/users/u5711205/Modular-STVCalculi/".
Require Export Parameters.
(*Import Params.
*)
(*Import Instantiation.*)

Module B (X: Params).
(* notation for type level existential quantifier *)
Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Close Scope Q_scope.

(*Variable cand: Type.*)

Module RatOrder  <: TotalLeBool.

  Definition t := ({v : list X.cand | (NoDup v) /\ ( [] <> v)} * Q)%type. (* (A * Q)%type. *)
  
  Definition leb (r1 : t) (r2 : t) := 
    match Q_dec (snd r1) (snd r2) with
    | inleft l => match l with
                  | left _ =>   true 
                  | right _ => false
                  end
    | inright r => true
    end.  
 
  Theorem leb_total : forall r1 r2, is_true (leb r1 r2) \/ is_true (leb r2 r1).
  Proof.   
    intros r1 r2. unfold is_true, leb.
    destruct (Q_dec (snd r1) (snd r2)). destruct s. auto.
    right.  destruct (Q_dec (snd r2) (snd r1)). destruct s. auto.
    pose proof (Qlt_trans (snd r1) (snd r2) (snd r1) q0 q).
    pose proof (Qlt_irrefl (snd r1)). unfold not in H0.
    pose proof (H0 H). inversion H1. auto. auto.
  Qed.
  
End RatOrder.

Module Import QSort := Sort RatOrder.



Definition Rat_eq r1 r2 := Qeq_bool r1 r2.



Fixpoint countem {A: Type} y (xs: list (A * Q)) : nat :=
   match xs with
   | [] => (0)%nat
   | x :: more => if Qeq_bool (snd x) y then S (countem y more) else (0)%nat
   end.

Lemma countem_len :
  forall (A : Type) (q : Q) (l : list (A * Q)), ((countem q l) <= length l)%nat.
Proof.
  intros. induction l.
  simpl. omega.
  simpl. destruct (Qeq_bool (snd a) q). omega. omega.
Qed.
  
Fixpoint take {A: Type} (y : nat) (xs: list (A * Q)) :=
   match y, xs with
   | O, _ => []
   | S y', [] => []
   | S y', x :: more => x :: take y' more
   end.

Fixpoint skip {A: Type} y (xs: list (A * Q)) :=
   match y, xs with
   | O, _ => xs
   | S y', [] => []
   | S y', x :: more => skip y' more
   end.

Lemma skip_bounded:
   forall (A: Type) (y: nat) xs, (length (@skip A y xs) <= length xs)%nat.
Proof.
   intros A y xs. revert y.
   induction xs; intros; simpl.
   - destruct y; simpl; omega.
   - destruct y; simpl; try omega.
     rewrite IHxs. omega.
Qed.

Lemma take_skip:
   forall (A: Type) k (xs : list (A * Q)) , (take k xs ++ skip k xs = xs)%nat.
Proof.
   intros A k xs. revert k.
   induction xs; intros; simpl.
   - destruct k; simpl; auto.
   - destruct k; simpl; auto.
     rewrite IHxs. auto.
Qed.

Function groupbysimple {A: Type} (xs: list (A * Q)) { measure length xs } :=
   match xs with
   | [] => []
   | x :: more =>
        let k := countem (snd x) more in
        (x :: take k more) :: @groupbysimple A (skip k more)
   end.
Proof.
   intros.
   simpl.
   assert (length (skip (countem (snd x) more) more) <= length more)%nat by
       apply skip_bounded. intuition.
Defined.


Fixpoint concat {A: Type} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x l => x ++ concat l
  end.

Lemma groupby_identity:
   forall (A : Type) xs, concat (groupbysimple A xs) = xs.
Proof.
  intros. 
  functional induction (groupbysimple A xs).
  - simpl. auto.
  - simpl. rewrite IHl. rewrite take_skip. auto.
Qed.


Lemma concat_rat:
  forall (l : list ({v : list X.cand | (NoDup v) /\ ( [] <> v)} * Q)) ,
    length l = length (concat (groupbysimple _ (sort l))).
Proof.
  intros l.
  pose proof (groupby_identity _ (sort l)).
  rewrite H.
  pose proof (Permuted_sort l).
  pose proof (Permutation_length).
  pose proof (H1 _ l (sort l) H0).
  auto.
Qed.

(*Eval compute in groupbysimple _ [(1%nat,(3 # 1)%Q); (1%nat,(3 # 1)%Q); (1%nat,(2 # 1)%Q); (0%nat,(2 # 3)%Q); (1%nat,(2 # 1)%Q)].
Eval compute in groupbysimple _ [(1%nat, (3 # 1)%Q)].
*)
 
Lemma groupby_notempty :
  forall  (A : Type) (l : list (A * Q)),
    l <> [] -> last (groupbysimple _ l) [] <> [].
Proof.
  intros A l H.
  functional induction (groupbysimple A l).
  + firstorder. 
  + simpl in *.
    remember (skip (countem (snd x) more) more) as skl.
    assert ({skl = []} + {skl <> []}). 
    pose proof (destruct_list skl). destruct X. destruct s.
    destruct s. right. rewrite e. intuition. inversion H0.
    left. auto.
    destruct H0. rewrite e. firstorder.
    pose proof (IHl0 n).
    pose proof (destruct_list skl). destruct X. destruct s.
    destruct s. rewrite e.
    rewrite (groupbysimple_equation A (x0 :: x1)).
    rewrite e in H0. rewrite (groupbysimple_equation _ (x0 :: x1)) in H0.
    auto. rewrite e in n. firstorder.
Qed.

Lemma sortedList_notempty :
  forall (l : list ({v : list X.cand | NoDup v /\ [] <> v} * Q)),
    l <> [] -> sort l <> [].
Proof.
  intros l H.
  remember (sort l) as t.
  induction t.
  pose proof (destruct_list l). destruct X. destruct s.
  destruct s. rewrite e in Heqt.
  pose proof (Permuted_sort l). rewrite e in H0.
  rewrite <- Heqt in H0.
  pose proof (Permutation_sym H0).
  pose proof (Permutation_nil H1). rewrite H2 in e.
  rewrite e in H. unfold not in H. pose proof (H eq_refl).
  inversion H3. firstorder.
  firstorder.
Qed.
  
  
Lemma sherin:
  forall (l : list ({v : list X.cand | NoDup v /\ [] <> v} * Q)),
    l <> [] ->
    last (groupbysimple _ (sort l)) [] <> [].
Proof.
  intros l H. pose proof (groupby_notempty _ (sort l) (sortedList_notempty l H)).
  auto.
Qed.

Lemma groupbysimple_not_empty: forall (l : list (list ({v : list X.cand | NoDup v /\ [] <> v} * Q))), 
       last l []  <> [] -> l <> [].
Proof.
 intros.
 intro.
 rewrite H0 in H.
 simpl in H.
 contradict H.
 auto.
Qed.


(* Section genericTermination.
Close Scope Q_scope. *) 
 
(*Module Base.*)
(*Close Scope Q_scope.*) 

(*
(*Variable cand: Type.*)
Variable cand_all: list cand.
Hypothesis cand_nodup: NoDup cand_all.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.
Hypothesis cand_in_dec: forall c : cand, forall l : list cand, {In c l} + {~In c l}.
*)
(* a ballot is a permutation of the list of candidates and a transfer balue *)

 Definition ballot :=  ({v : list X.cand | (NoDup v) /\ ( [] <> v)} * Q).

(*
Variable bs : list ballot.
Variable st : nat. 
Variable quota : Q.
*)

Definition length_empty: length ([]:list X.cand) <= X.st.
Proof.
 simpl.
 induction X.st.
 auto.
 auto.
Defined.

Definition nbdy : list X.cand := [].                    (* empty candidate list *)
Definition nty  : X.cand -> Q := fun x => (0)%Q .          (* null tally *)
Definition nas  : X.cand -> list (list ballot) := fun x => []. (* null vote assignment *)
Definition emp_elec : {l: list X.cand | length l <= X.st} := 
 exist _ ([] :list X.cand) length_empty.                (*empty list of elected candidates*)
Definition all_hopeful  := 
 exist (fun v => NoDup v) X.cand_all X.cand_nodup.           (*inintial list of all candidates*)


(*
Fixpoint have_same_val (r: Q) (l: (list ballot)) acc :=
 match l with 
  [] => acc
 |l0 :: ls => if Rat_eq r (snd l0) then have_same_val r ls (l0:: acc) else acc 

 end.


Fixpoint Remove_ballotSame_rat (r: Q) (l: list ballot) acc :=
  match l with 
   [] => acc
 |l0 :: ls => if Rat_eq r (snd l0) then Remove_ballotSame_rat r ls acc
                  else Remove_ballotSame_rat r ls (l0:: acc)
 end.

Fixpoint Parcel_same_val (n:nat) l :=
 match n with
    O => []
   |S n' => match l with 
                 [] => []
               | l0:: ls => (have_same_val (snd l0) (l0::ls) []) 
                                :: (Parcel_same_val n' (Remove_ballotSame_rat (snd l0) ls []))
            end
   end.
  

*)

(* sum of weights in a list of ballots *)
Fixpoint sum_aux (l : list ballot) (acc:Q): Q :=
 match l with 
            | [] => acc
            | l :: ls => sum_aux ls (Qred ((snd l) + acc)%Q)
 end. 

Definition sum (l:list ballot) := sum_aux l (0).

Fixpoint SUM_AUX (l: list (list ballot)) (acc:Q): Q := 
 match l with
          | [] => acc
          | l0 :: ls => SUM_AUX ls (Qred ((sum l0) + acc)%Q)
 end. 

Definition SUM (l: list (list ballot)) := SUM_AUX l 0.

Fixpoint is_elem (l:list X.cand) (c : X.cand) :=
 match l with
           [] => false
           |l0::ls => if X.cand_eq_dec l0 c then true else is_elem ls c
 end.

(*checks if list l has duplicate elements*)
Fixpoint nodup_elem (l:list X.cand) :=
 match l with
          [] => true
          |l0::ls => if is_elem ls l0 
                       then false
                     else nodup_elem ls      
 end. 

Fixpoint non_empty (l:list X.cand):=
 match l with 
         [] => false
         |_ => true
 end.


(*filters ballots so that only formal ballots remain*)
Fixpoint Filter (l: list ballot):=
 match l with
         [] => []
         |l0::ls => let x := proj1_sig (fst l0) in
                      if X.ValidBallot x
                         then l0:: Filter ls
                      else Filter ls  
 end.


Fixpoint Sum_nat (l: list nat) :=
 match l with
   [] => (0)%nat
  |l0::ls => (l0 + Sum_nat ls)%nat
end.

Lemma map_cons: forall (A: Type) (l: list A) (x: A) (f: A -> nat), map f (x::l) = (f x) :: map f l. 
Proof.
intros.
induction l.
simpl. auto.
simpl.
auto.
Qed.

Lemma map_ext_in {A B} (f f' : A -> B) (ls : list A)
        (H : forall a, In a ls -> f a = f' a)
    : map f ls = map f' ls.
  Proof.
    induction ls; simpl; trivial.
    rewrite H, IHls.
    { reflexivity. }
    { intros; apply H; right; assumption. }
    { left; reflexivity. }
  Qed.

Lemma SumNat_app: forall l1 l2, Sum_nat (l1 ++ l2) = (Sum_nat l1 + (Sum_nat l2))%nat.
Proof.
intros.
induction l1.
simpl.
reflexivity.
simpl.
rewrite IHl1.
omega.
Qed.

Lemma sum_less_than : forall (f: X.cand -> nat) (f' : X.cand -> nat) (h: list X.cand) c,
 (forall d, d <> c -> (f d = f' d)) -> (f' c < f c)%nat -> (In c h) -> (NoDup h) ->
 (Sum_nat (map f' h) < Sum_nat (map f h))%nat.
Proof.
intros f f' h c H1 H2 H3 H12.
(*destruct H as [H1 [H2 [H3 H12]]].*)
specialize (in_split c h H3). intros H4. destruct H4 as [h1 [h2 H5]].
rewrite H5.
assert (hyp: forall g: X.cand -> nat, map g (h1++ c:: h2) = (map g h1) ++ ([g c] ++ (map g h2))). intro g.
rewrite map_app.
assert (hyp2: map g (c:: h2) = (g c) :: map g h2).
rewrite map_cons. auto.
rewrite hyp2.
apply (app_inv_head (map g h1)).
simpl. auto.
specialize (hyp f).
assert (hyp': forall g': X.cand -> nat, map g' (h1++ c:: h2) = (map g' h1) ++ ([g' c] ++ (map g' h2))). intro g'.
rewrite map_app.
assert (hyp2: map g' (c:: h2) = (g' c) :: map g' h2).
rewrite map_cons. auto.
rewrite hyp2.
apply (app_inv_head (map g' h1)).
simpl. auto.
specialize (hyp' f').
rewrite hyp.
rewrite hyp'.
simpl.
assert (hyp3: ~ In c h1).
rewrite H5 in H12.
specialize (NoDup_remove_2 h1 h2 c H12). intro NoduplicateH1H2.
intro.
apply NoduplicateH1H2.
apply in_or_app.
left;assumption.
assert (hyp4: forall d, In d h1 -> f d = f' d).
intros d auxHyp.
assert (auxHyp2: d <> c).
intro.
rewrite H in auxHyp.
contradiction hyp3.
apply H1. assumption.
assert (hyp5: ~ In c h2). 
rewrite H5 in H12.
specialize (NoDup_remove_2 h1 h2 c H12). intro.
intro.
apply H.
apply in_or_app.
right;auto.
assert (hyp6: forall d, In d h2 -> f d = f' d).
intros.
assert (auxhyp: d <> c).
intro.
rewrite H0 in H.
apply hyp5. assumption.
apply H1. auto.
specialize (map_ext_in f f' h1 hyp4). intro HH.
specialize (map_ext_in f f' h2 hyp6). intro HH'.
rewrite HH.
rewrite HH'.
assert (hyp7: Sum_nat (map f' h1 ++ f c:: map f' h2) = (Sum_nat (map f' h1) + (f c) + (Sum_nat (map f' h2)))%nat).
rewrite SumNat_app.
simpl.
omega.
assert (hyp8: Sum_nat (map f' h1 ++ f' c:: map f' h2) = (Sum_nat (map f' h1) + (f' c) + (Sum_nat (map f' h2)))%nat). 
rewrite SumNat_app.
simpl.
omega.
rewrite hyp7.
rewrite hyp8.
omega.
Qed.


(* we can find a candidate with least no of first prefs *)
Lemma list_min : forall A:Type, forall l: list A, forall f: A -> Q,
 (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->(f m <= f b)%Q))).
Proof.
 intros.
 induction l as [ | l ls ].
 left. trivial.
 destruct IHls.
 right.
 exists l. split.
 apply (in_eq l ls). intros b ass.
 assert (l = b \/ In b ls).
 apply (in_inv ass). destruct H. replace l with b. intuition. replace ls with ([] : list A) in H.
 contradict H.
 right. destruct s. destruct a. 
 assert (sumbool ((f x < (f l))%Q) (((f l) <= (f x))%Q)).
 apply (Qlt_le_dec (f x) (f l))%Q.
 assert (sumbool ((f x <= (f l))%Q) (((f l) <= (f x))%Q)).
 intuition.
 destruct H2.
  (* x is the minimum *)
 exists x. split.
 apply (in_cons l x ls). assumption. intros b ass.
 assert (l = b \/ In b ls).
 apply (in_inv ass).
 destruct H2. replace b with l. assumption.
 apply (H0 b H2).
  (* l is the minimum *)
 exists l. split.
 apply (in_eq l ls).
 intros b ass.
 assert (l = b \/ In b ls). apply (in_inv ass). destruct H2. 
 replace l with b. intuition.
 specialize (H0 b H2).
 apply (Qle_trans (f l) (f x) (f b)). assumption. assumption.
Defined. 

(*if a list is not empty, then there exist an element which has the greatest value w.r.t. function f*)
Lemma list_max : forall A:Type, forall l: list A, forall f: A -> Q,
   (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->(f b <= f m)%Q))).
Proof.
 intros.
 induction l.
 left;auto.
 destruct IHl.
 right.
 subst.
 exists a.
 split.
 simpl;left;auto.
 intros.
 destruct H.
 subst.
 apply (Qle_refl (f b)).
 inversion H.
 right.
 destruct s.
 destruct a0.
 assert (sumbool ((f a < f x)%Q) ((f x <= f a)%Q)).
 apply (Qlt_le_dec (f a) (f x)).
 destruct H1.
 exists x.
 split.
 right;auto.
 intros.
 assert (a= b \/ In b l) by apply (in_inv H1).
 destruct H2.
 subst.
 destruct H1.
 apply (Qlt_le_weak (f b)(f x)).
 assumption.
 apply H0.
 auto.
 apply H0.
 auto.
 exists a.
 split.
 left;auto.
 intros.
 assert (a=b \/ In b l) by apply (in_inv H1).
 destruct H2.
 rewrite H2.
 apply (Qle_refl (f b)).
 apply (Qle_trans (f b)(f x)(f a)).
 apply H0.
 auto.
 assumption.
Qed.

Lemma list_max_cor: forall A:Type, forall l: list A, forall f: A -> Q,[]<> l -> existsT m:A, (In m l /\ (forall a:A, In a l -> (f a <= f m)%Q)). 
Proof.
 intros.
 specialize (list_max A l f).
 intros.
 destruct X.
 rewrite e in H.
 contradiction H.
 auto.
 assumption.
Qed.


(*Section Generic_Machine.*)

(* initial, intermediate and final states in vote counting *)

 Inductive Machine_States :=
  initial:
     list ballot -> Machine_States 
  |state:                                             (** intermediate states **)
    list ballot                                       (* uncounted votes *)
    * list (X.cand -> Q)                              (* tally *)
    * (X.cand -> list (list ballot))                  (* pile of ballots *)
    * ((list X.cand) * (list X.cand))                 (* backlog *)
    * {elected: list X.cand | length  elected <= X.st}(* elected candidates *)
    * {hopeful: list X.cand | NoDup hopeful}          (* continuing candidates *)
      -> Machine_States
  |winners:                                           (** final state **)
      list X.cand -> Machine_States.                   (* election winners *)

Definition State_final (a : Machine_States) : Prop :=
 exists w, a = winners (w).

Definition State_initial (a : Machine_States) : Prop :=
 exists (ba : list ballot), a = initial (ba).

Lemma final_dec: forall j : Machine_States, (State_final j) + (not (State_final j)).
Proof. 
 intro j. 
  destruct j;
   repeat (right;unfold State_final;unfold not;intro H;destruct H;discriminate) 
     || 
       left;unfold State_final;exists l;reflexivity.
Defined.

Lemma initial_dec: forall j: Machine_States, (State_initial j) + not (State_initial j).
Proof.
 intro j.
  destruct j;
    repeat (left;unfold State_initial;exists l;reflexivity)
        ||
          (right;intro H;inversion H; discriminate).
Qed.        
 

(* Rules *)
Definition FT_Rule := Machine_States -> Machine_States -> Prop.

(* The set (nat)^5 to be used as the set on which we impose a lexicographic order *)
Definition Product_Five_NatSet := nat * (nat * (nat * (nat * nat))). 

 Definition DependentNat_Prod2 := sigT (A:= nat) (fun a => nat).
 Definition DependentNat_Prod3 := sigT (A:= nat) (fun a => DependentNat_Prod2).
 Definition DependentNat_Prod4 := sigT (A:= nat) (fun a => DependentNat_Prod3).
 Definition DependentNat_Prod5 := sigT (A:= nat) (fun a => DependentNat_Prod4).

 Definition Make_DependentNat2  :
   nat * nat -> DependentNat_Prod2.
  intros (p,q).
  exists p.
  exact q.
 Defined.

 Definition Make_DependentNat3 :
   nat * (nat * nat) -> DependentNat_Prod3.
  intros (n, p_q).
  exists n.
  exact (Make_DependentNat2 p_q).
 Defined. 

 Definition Make_DependentNat4 :
   nat * (nat * (nat * nat)) -> DependentNat_Prod4.
  intros (m, n_p_q).
  exists m.
  exact (Make_DependentNat3 n_p_q).
 Defined.

 Definition Make_DependentNat5 :
   nat * (nat * (nat * (nat * nat))) -> DependentNat_Prod5.
  intros (m,n_p_q_r).
  exists m.
  exact (Make_DependentNat4 n_p_q_r).
 Defined.

 Definition LexOrdNat_Aux1 :
 DependentNat_Prod2 -> DependentNat_Prod2 -> Prop :=
 (lexprod nat (fun a => nat) Peano.lt (fun a:nat =>Peano.lt)).

 Definition LexOrdNat_Aux2 :
 DependentNat_Prod3 -> DependentNat_Prod3 -> Prop :=
 (lexprod nat (fun a => DependentNat_Prod2) Peano.lt (fun a:nat =>LexOrdNat_Aux1)).

 Definition LexOrdNat_Aux3 :
 DependentNat_Prod4 -> DependentNat_Prod4 -> Prop:=
 (lexprod nat (fun a => DependentNat_Prod3) Peano.lt (fun (a:nat) => LexOrdNat_Aux2)).

 Definition LexOrdNat:
 DependentNat_Prod5 -> DependentNat_Prod5 -> Prop :=
 (lexprod nat (fun a => DependentNat_Prod4) Peano.lt (fun (a:nat) => LexOrdNat_Aux3)).

Lemma wf_Lexprod1 : well_founded LexOrdNat_Aux2.
 unfold LexOrdNat_Aux2. apply wf_lexprod.
 apply lt_wf.
 intro n.
 unfold LexOrdNat_Aux1;apply wf_lexprod.
 apply lt_wf.
 intro m; apply lt_wf.
Qed.

(*LexOrdNat_Aux3 is a well founded ordering*)
Lemma wf_Lexprod : well_founded LexOrdNat_Aux3.
Proof.
 red in |-*;apply wf_lexprod. apply lt_wf. intro n.
 red in |-*;apply wf_lexprod. apply lt_wf. intro m.
 red in |-*;apply wf_lexprod. apply lt_wf. intro p.
 apply lt_wf.
Qed.

 Lemma wf_LexOrdNat : well_founded LexOrdNat.
 Proof.
  red in |-*; apply wf_lexprod. apply lt_wf. intro n.
  red in |-*; apply wf_lexprod. apply lt_wf. intro m.
  red in |-*; apply wf_lexprod. apply lt_wf. intro p.
  red in |-*; apply wf_lexprod. apply lt_wf. intro r.
  apply lt_wf.
 Qed.

(* imposing a well-found ordering on (nat)^5 *)

  Definition Order_NatProduct : Product_Five_NatSet -> Product_Five_NatSet -> Prop :=
    (fun x y : nat * (nat * (nat * (nat * nat))) =>
     LexOrdNat (Make_DependentNat5 x) (Make_DependentNat5 y)).

Lemma Order_NatProduct_wf : well_founded Order_NatProduct.
 unfold Order_NatProduct. 
 apply wf_inverse_image.
 apply wf_LexOrdNat.
Qed.



(* measure function maps to ({0,1},length h, Sum (map (\.c -> length (concat p c)) snd bl), length bl, length ba) *)

 Definition Measure_States: {j:Machine_States |not (State_final j)} -> Product_Five_NatSet.
  intro H. destruct H as [j ej]. destruct j.
  split. exact 1.
  split. exact 0. split. exact 0. split. exact 0. exact 0.
  destruct p as [[[[[ba t] p] bl] e] h].
  split. exact 0.
  split. exact (length (proj1_sig h)).
  split. exact (Sum_nat (map (fun c => length (concat (p c))) (snd bl)))%nat.
  split. exact (length (fst bl)). exact (length ba).
  contradiction ej.
  unfold State_final. 
  exists l. reflexivity.
 Defined.

(* lexicographic order behaves as expected *)

 Lemma wfo_aux:  forall a b c d a' b' c' d' e e': nat,
     (LexOrdNat (Make_DependentNat5 (a, (b, (c, (d,e)))))
                (Make_DependentNat5 (a', (b', (c',(d',e')))))) <->
     (a < a' \/
     (a = a' /\ b < b' \/
     (a = a' /\ b = b' /\ c < c' \/
     (a = a' /\ b = b' /\ c = c' /\ d < d' \/
     (a = a' /\ b = b' /\ c = c' /\ d = d' /\ e < e'))))).

 Proof.
 intros. split. unfold LexOrdNat. unfold Make_DependentNat5. simpl. intro H. inversion H. subst. 
  (* case 1st component are below one another *)
 auto.
  (* case 1st components are equal *)
 unfold LexOrdNat_Aux3 in H1. inversion H1. subst. auto.
  (* case 1st and 2nd components are equal and 3rd are below one another *)
  unfold LexOrdNat_Aux2 in H6.
  inversion H6.
  right;right;left;auto.
  (* case where the first three components are equal but the last decreases*)
  unfold LexOrdNat_Aux1 in H11. inversion H11. subst.
  right;right;right;auto.        
  (* the case where the first four are equal and the last decreases *)
  right;right;right;right. subst. auto.
  (* right-to-left direction *)
 intro H. destruct H.
  (* case 1st components are below one another *)
 unfold LexOrdNat. apply left_lex. assumption.
 destruct H.
  (* case 1st components are equal and 2nd components are below one another *)
 destruct H as [H1 H2]. subst. apply right_lex. apply left_lex. assumption.
  (* case 1st and 2nd components are identical, and 3rd components are below one another *)
 destruct H as [H1 | H2]. destruct H1 as [H11 [H12 H13]]. subst. repeat apply right_lex || apply right_lex || apply left_lex. assumption. destruct H2 as [H1 | H2]. destruct H1 as [H11 [H12 [H13 H14]]]. subst.
 repeat apply right_lex || apply right_lex || apply left_lex. auto.
 destruct H2 as [H21 [H22 [H23 [H24 H25]]]]. subst. repeat apply right_lex. assumption.
Qed.

Definition IsNonFinal: forall j: Machine_States, forall e: not (State_final j), { j : Machine_States | not (State_final j) }.
  intros j e. exists j. assumption.
Defined.




(*
Definition Is_Legitimate_Elim_two (R: Machine_States -> Machine_States -> Prop) :=
   (forall premise, forall t p e h r, (premise = state ([],t, p, [], e, h, r)) ->
     (exists c, In c r /\
       (p c) <> [] ) -> exists conc, R premise conc)  *
   (forall premise conclusion, R premise conclusion ->
     exists nba t p np e h r,
     (premise = state ([], t, p, [], e, h, r)) /\
     exists c, In c (proj1_sig h) /\ (length (np c)) < (length (p c)) /\
     (forall d, d <> c -> length (np d) = length (p d)) /\   
     (conclusion = state (nba, t, np, [], e, h, r))).

Lemma dec_ElimTwo : forall R (p c : Machine_States),
 (Is_Legitimate_Elim_two R) -> R p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
intros R p c ss Hr ep ec.
unfold Is_Legitimate_Elim_two in ss.
destruct ss as [ss1 s1].
specialize (s1 p c Hr).
destruct s1 as [nba [t [p0 [np [e [h [r s11]]]]]]]. 
destruct s11 as [Hs1 [weak Hs3]].
destruct Hs3 as [Hs31 [Hs32 [Hs33 Hs34]]].
destruct p.
inversion Hs1.
destruct c. inversion Hs34.
destruct p as [[[[[[ba11 t11] p11] bl11] e11] h11] r11].
destruct p1 as [[[[[[ba22 t22] p22] bl22] e22] h22] r22].
inversion Hs1. inversion Hs34. subst.
unfold Measure_States.
simpl.
unfold Order_NatProduct.
rewrite wfo_aux.
right;left. split. auto.
assert (hypo: forall d, d <> weak -> length (p0 d) = length (np d)).
intros.
specialize (Hs33 d H).
rewrite Hs33. auto.
specialize (sum_less_than (fun c => length (p0 c)) (fun c' => length (np c')) (proj1_sig h) 
                          weak hypo Hs32 Hs31 (proj2_sig h)). intro.
omega.
inversion Hs34.
inversion Hs1.
Qed.
*)  
Definition SanityCheck_Initial_App (R : Machine_States -> Machine_States -> Prop) :=  
  forall premise, forall ba, (premise = initial ba) -> existsT conclusion,
     (conclusion = state (Filter ba, [nty], nas, (nbdy,nbdy), emp_elec, all_hopeful)) *  
      R premise conclusion.

Definition SanityCheck_Initial_Red (R : Machine_States -> Machine_States -> Prop) := 
  forall p c, R p c -> exists ba ba' t ass bl e h, (p = initial ba) /\
  (c = state (ba', t, ass, bl, e, h)).

Definition SanityCheck_Count_App (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise, forall ba t p  bl h e , (premise = state (ba, t, p ,bl ,e, h)) -> (ba <> []) ->
    existsT conclusion, (R premise conclusion)).

Definition SanityCheck_Count_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall (p: Machine_States) (c: Machine_States), R p c -> exists ba1 ba2 t1 t2 p1 p2 bl e h, 
   (p = state (ba1, t1, p1, bl, e, h)) /\ 
   (c = state (ba2, t2 :: t1, p2, bl, e, h)) /\ 
   ( length ba2 < length ba1) /\
   (Sum_nat (map (fun c => length (concat (p1 c))) (snd bl)) = 
         (Sum_nat (map (fun c => length (concat (p2 c))) (snd bl))))).
(*
Definition Is_empty (l : list cand) :=
 match l with
   [] => true
  |_ => false
end.
*)
(* note that I have put the null tally as the default value for head in case of empty list *)

(* --------------------------------------------------------------------------------- *)
  (* If we wish to keep the list of eliminated in the bl2 all the way up to the
     end, then we need to consider the case that concatening the pile of the head of bl2 is 
       not empty so that we know which one of transfer-elected r transfer-removed should
        correctly be applied. There is a cleaner way and that is to simply either allow the
         bl2 to be empty or just include the most recently excluded candidate. This way we
          can get rid of considering if concat of pile of head of bl2 is empty or not by
            including a simpler check inside the transfer-excluded that ensures the 
              updated the head of the updated bl2 has some votes in it to distribute still *)
(* 
Definition SanityCheck_Transfer1_App (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise, forall t p (bl: (list X.cand) * (list X.cand)) e h, 
 (premise = state ([], t, p, (fst bl, []), e, h)) -> (length (proj1_sig e) < X.st) /\ 
 (fst bl <> []) /\ (forall c, In c (proj1_sig h) -> ((hd nty t) c < X.quota)%Q) -> 
    existsT conc, R premise conc).

Definition SanityCheck_Transfer2_App (R: Machine_States -> Machine_States -> Prop) :=
 forall premise, forall t p bl1 bl2 c e h , (premise = state ([], t, p, (bl1, c::bl2), e, h)) ->
 (length (proj1_sig e) < X.st) /\ (bl1 <> []) /\ (concat (p c) = []) /\ 
 (forall c, In c (proj1_sig h) -> ((hd nty t) c < X.quota)%Q) ->
     existsT conc, R premise conc.

Definition SanityCheck_Transfer3_App (R: Machine_States -> Machine_States -> Prop) :=
 forall premise, forall t p bl1 bl2 c e h , (premise = state ([], t, p, (bl1, c::bl2), e, h)) ->
 (length (proj1_sig e) < X.st) /\ (bl1 <> []) /\ (concat (p c) <> []) /\ 
 (forall c, In c (proj1_sig h) -> ((hd nty t) c < X.quota)%Q) ->
     existsT conc, R premise conc.
*)

Definition SanityCheck_TransferElected_App (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise, forall t p (bl: (list X.cand) * (list X.cand)) e h, 
 (premise = state ([], t, p, (fst bl, []), e, h)) -> (length (proj1_sig e) < X.st) /\ 
 (fst bl <> []) /\ (forall c, In c (proj1_sig h) -> ((hd nty t) c < X.quota)%Q) -> 
    existsT conc, R premise conc).

Definition SanityCheck_TransferRemoved_App (R: Machine_States -> Machine_States -> Prop) :=
 forall premise, forall t p bl1 bl2 c e h , (premise = state ([], t, p, (bl1, c::bl2), e, h)) ->
 (length (proj1_sig e) < X.st) /\  
 (forall c, In c (proj1_sig h) -> ((hd nty t) c < X.quota)%Q) ->
     existsT conc, R premise conc.

 
Definition SanityCheck_TransferElected_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise conclusion, R premise conclusion ->
   exists nba t p np bl nbl h e,
   (premise = state ([], t, p, bl, e, h)) /\
   (length (fst nbl) < length (fst bl)) /\ 
       (Sum_nat (map (fun c => length (concat (p c))) (snd bl)) = 
             Sum_nat (map (fun c => length (concat (np c))) (snd nbl))) /\
    (conclusion = state (nba, t, np, nbl, e, h))). 

Definition SanityCheck_TransferRemoved_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise conclusion, R premise conclusion ->
   exists nba t p np bl nbl h e,
   (premise = state ([], t, p, bl, e, h)) /\
   (length (fst nbl) = length (fst bl)) /\ 
       (Sum_nat (map (fun c => length (concat (np c))) (snd nbl)) <  
             Sum_nat (map (fun c => length (concat (p c))) (snd bl))) /\
    (conclusion = state (nba, t, np, nbl, e, h))). 


Definition SanityCheck_Elect_App (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise, forall t p bl e h, (premise = state ([], t, p, bl, e, h)) ->
     (existsT (c: X.cand), 
     (length (proj1_sig e)) + 1 <= X.st /\  
     In c (proj1_sig h) /\ ((hd nty t) (c) >= X.quota)%Q) -> existsT conc, R premise conc).

Definition SanityCheck_Elect_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise conclusion, R premise conclusion ->
     exists t p np bl nbl e ne nh h, 
     (premise = state ([], t, p, bl, e, h)) /\
          (length (proj1_sig nh) < length (proj1_sig h)) /\
          (length (proj1_sig e) < length (proj1_sig ne)) /\
     (conclusion = state ([], t, np, nbl, ne, nh))).

(* I have made bl2 empty because of the decision above, namely that bl2 is either empty or 
   has at most one element in it at each time. Now a candidate is eliminated only if there is
   no vote to transfer either elected ones or removed one. *)
Definition SanityCheck_Elim_App (R: Machine_States -> Machine_States -> Prop) :=
  (forall premise, forall t p e h, (premise = state ([], t, p, ([], []), e, h)) ->
     length (proj1_sig e) + length (proj1_sig h) > X.st /\
     (forall c, In c (proj1_sig h) -> ((hd nty t) c < X.quota)%Q) -> existsT conc, R premise conc).

Definition SanityCheck_Elim_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise conclusion, R premise conclusion ->
     exists nba t p np e h nh bl2 nbl2,
     (premise = state ([], t, p, ([], bl2), e, h)) /\
     length (proj1_sig nh) < length (proj1_sig h) /\
     (conclusion = state (nba, t, np, ([], nbl2), e, nh))).

Definition SanityCheck_Hwin_App (R: Machine_States -> Machine_States -> Prop) :=
  (forall premise, forall ba t p bl e h, (premise = state (ba, t, p, bl, e, h)) ->
     length (proj1_sig e) + (length (proj1_sig h)) <= X.st -> existsT conc, R premise conc).


Definition SanityCheck_Hwin_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise conclusion, R premise conclusion ->
     exists w ba t p bl e h,
      (premise = state (ba, t, p, bl, e, h)) /\
      w = (proj1_sig e) ++ (proj1_sig h) /\ 
      (conclusion = winners w)).

Definition SanityCheck_Ewin_App (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise, forall ba t p bl e h, (premise = state (ba, t, p, bl, e, h)) ->
    length (proj1_sig e) = X.st -> existsT conc, R premise conc).

Definition SanityCheck_Ewin_Red (R: Machine_States -> Machine_States -> Prop) :=
 (forall premise conclusion, R premise conclusion ->
    exists w ba t p bl e h,
    (premise = state (ba, t, p, bl, e, h)) /\
     w = (proj1_sig e) /\ 
    (conclusion = winners (proj1_sig e))).

Record STV := 
   mkSTV {initStep: Machine_States -> Machine_States -> Prop;
          evidence_applicability_initStep: (SanityCheck_Initial_App initStep);
          evidence_reducibility_initStep: (SanityCheck_Initial_Red initStep);
          count: Machine_States -> Machine_States -> Prop;
          evidence_applicability_count: (SanityCheck_Count_App count);
          evidence_reducibility_count: (SanityCheck_Count_Red count);    
          transfer_elected: Machine_States -> Machine_States -> Prop;
          evidence_applicability_transferElected: (SanityCheck_TransferElected_App transfer_elected);
          evidence_reducibility_transferElected: (SanityCheck_TransferElected_Red transfer_elected);
        (*  transfer2_elected: Machine_States -> Machine_States -> Prop;
          evidence_applicability_transfer2_elected: (SanityCheck_Transfer2_App transfer2_elected);
          evidence_reducibility_transfer2_elected: (SanityCheck_Transfer_Red transfer2_elected); *)
          transfer_removed: Machine_States -> Machine_States -> Prop;
          evidence_applicability_transferRemoved: (SanityCheck_TransferRemoved_App transfer_removed);
          evidence_reducibility_transferRemoved: (SanityCheck_TransferRemoved_Red transfer_removed);
          elect: Machine_States -> Machine_States -> Prop;
          evidence_applicability_elect: (SanityCheck_Elect_App elect);
          evidence_reducibility_elect: (SanityCheck_Elect_Red elect);
          elim: Machine_States -> Machine_States -> Prop;
          evidence_applicability_elim: (SanityCheck_Elim_App elim);
          evidence_reducibility_elim: (SanityCheck_Elim_Red elim);
          hwin: Machine_States -> Machine_States -> Prop;
          evidence_applicability_hwin: (SanityCheck_Hwin_App hwin);
          evidence_reducibility_hwin: (SanityCheck_Hwin_Red hwin);         
          ewin: Machine_States -> Machine_States -> Prop;
          evidence_applicability_ewin: (SanityCheck_Ewin_App ewin);
          evidence_reducibility_ewin: (SanityCheck_Ewin_Red ewin)}.

(* beginning of measure decreasing proof for new formalised rules*)
Lemma dec_Initial : forall (s: STV) (p c : Machine_States),
 initStep s p c  -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof. 
 intros s p c H ep ec.
 destruct s. 
 simpl in H.
 unfold SanityCheck_Initial_Red in evidence_reducibility_initStep0.
 destruct p.
 destruct c.
 specialize (evidence_reducibility_initStep0 (initial l) (initial l0)).
 intuition.
 destruct H0 as [ba [ba' [t [ass [bl [e [h [Hev21 Hev22]]]]]]]].
 inversion Hev22. 
 destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite wfo_aux.
 left;auto.
 contradict ec. unfold State_final. exists l0. reflexivity.
 specialize (evidence_reducibility_initStep0 (state p) c).
 intuition.
 destruct H0 as [ba [ba' [t [ass [bl [e1 [h1 [Hev21 Hev22]]]]]]]].
 inversion Hev21.
 contradict ep. unfold State_final. exists l. auto.
Qed.

Lemma dec_Count : forall (s: STV) (p c : Machine_States),
 count s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s. 
 simpl in Hr.
 unfold SanityCheck_Count_Red in evidence_reducibility_count0.
 specialize (evidence_reducibility_count0 p c Hr).
 destruct  evidence_reducibility_count0 as [ba1 [ba2 [t1 [t2 [p1 [p2 [bl [e [h Hev21]]]]]]]]].
 destruct Hev21 as [Hev211 [Hev22 [Hev23 Hev24]]].
 destruct p. 
 inversion Hev211.
 destruct c.
 inversion Hev22.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p0 as [[[[[ba22 t22] p22] bl22] e22] h22].
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite -> wfo_aux.
 inversion Hev22. inversion Hev211. subst. 
 right. right. right. right.
 split. auto.
 split.  auto. rewrite Hev24. auto.
 contradict ec.
 unfold State_final. exists l. reflexivity.
 contradict ep. exists l. auto.
Qed.

Lemma dec_TransferElected : forall (s: STV) (p c : Machine_States),
 transfer_elected s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s. 
 simpl in Hr.
 unfold SanityCheck_TransferElected_Red in evidence_reducibility_transferElected0.
 specialize (evidence_reducibility_transferElected0 p c Hr).
 destruct evidence_reducibility_transferElected0 as [nba [t [p0 [np [bl [nbl [h [e [Hev21 [Hev22 [Hev22' Hev23]]]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev21. inversion Hev23. subst.
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite -> wfo_aux.
 (* destruct Hev22 as [Hev221 | Hev222]. *)
 right; right;right; left. intuition.
(* right; right; left.  intuition. *) 
 contradict ec; unfold State_final; exists l ;auto.
 contradict ep; exists l; auto.
Qed.

(*
Lemma dec_TransferElected2 : forall (s: STV) (p c: Machine_States),
 transfer2_elected s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s. 
 simpl in Hr.
 unfold SanityCheck_Transfer_Red in evidence_reducibility_transfer2_elected0.
 specialize (evidence_reducibility_transfer2_elected0 p c Hr).
 destruct evidence_reducibility_transfer2_elected0 as 
             [nba [t [p0 [np [bl [nbl [h [e [Hev21 [Hev22 Hev23]]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev21. inversion Hev23. subst.
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite -> wfo_aux.
 destruct Hev22 as [Hev221 | Hev222].
 right; right;right; left. intuition.
 right; right; left.  intuition. 
 contradict ec; unfold State_final; exists l ;auto.
 contradict ep; exists l; auto.
Qed.
*)

Lemma dec_TransferRemoved : forall (s: STV) (p c : Machine_States),
 transfer_removed s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s. 
 simpl in Hr.
 unfold SanityCheck_TransferRemoved_Red in evidence_reducibility_transferRemoved0.
 specialize (evidence_reducibility_transferRemoved0 p c Hr).
 destruct evidence_reducibility_transferRemoved0 as [nba [t [p0 [np [bl [nbl [h [e [Hev21 [Hev22 [Hev22' Hev23]]]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev21. inversion Hev23. subst.
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite -> wfo_aux.
 (* destruct Hev22 as [Hev221 | Hev222]. *)
 right; right; left. intuition.
 (* right; right; left.  intuition. *) 
 contradict ec; unfold State_final; exists l ;auto.
 contradict ep; exists l; auto.
Qed.
 
Lemma dec_Elect : forall (s: STV) (p c : Machine_States),
 elect s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold SanityCheck_Elect_Red in evidence_reducibility_elect0.
 specialize (evidence_reducibility_elect0 p c Hr).
 destruct evidence_reducibility_elect0 as [t [p0 [np [bl [nbl [e [ne [nh [h [Hev1 [Hev2 [Hev3 Hev4]]]]]]]]]]]].
 destruct c.
 inversion Hev4.
 destruct p.
 inversion Hev1.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev1. inversion Hev4. subst.
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite -> wfo_aux.
 right; left.  intuition.
 inversion Hev1. 
 inversion Hev4.
Qed.

Lemma dec_Elim : forall (s: STV) (p c : Machine_States),
 elim s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold SanityCheck_Elim_Red in evidence_reducibility_elim0.
 specialize (evidence_reducibility_elim0 p c Hr).
 destruct evidence_reducibility_elim0 as [nba [t [p0 [np [e [h [nh [bl2 [nbl2 H]]]]]]]]].
 destruct p.
 destruct H as [HH HHH].
 inversion HH.
 destruct c.
 destruct H as [HH [HHH1 HHH2]].
 inversion HHH2.
 destruct p as [[[[[nba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[nb222 t22] p22] bl22] e22] h22].
 destruct H as [K1 [K2 K3]].
 inversion K1.
 inversion K3.
 subst.
 unfold Measure_States.
 simpl.
 unfold Order_NatProduct.
 rewrite wfo_aux.
 right;left. intuition.
 contradict ec; exists l; reflexivity.
 contradict ep; exists l; auto.
Qed.

Lemma dec_Hwin  : forall (s: STV) (p c : Machine_States),
 hwin s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold SanityCheck_Hwin_Red in evidence_reducibility_hwin0.
 specialize (evidence_reducibility_hwin0 p c Hr).
 destruct evidence_reducibility_hwin0 as [w [ba [t [p0 [bl [e [h [Hev21 [Hev22 Hev23]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 inversion Hev23.
 contradict ec; exists l; reflexivity.
 contradict ep; exists l; auto.
Qed.

Lemma dec_Ewin : forall (s: STV) (p c : Machine_States),
 ewin s p c -> forall (ep : ~ State_final p) (ec : ~ State_final c),
Order_NatProduct (Measure_States (IsNonFinal c ec))
  (Measure_States (IsNonFinal p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold SanityCheck_Ewin_Red in evidence_reducibility_ewin0.
 specialize (evidence_reducibility_ewin0 p c Hr).
 destruct evidence_reducibility_ewin0 as [w [ba [t [p0 [e [h [Hev21 [Hev22 [Hev23 Hev24]]]]]]]]].
 destruct p.
 inversion Hev21.
 inversion Hev22.
 destruct c.
 inversion Hev24.
 inversion Hev24.
 contradict ec; exists l; auto.
 contradict ep; exists l; auto.
Qed.
   
 
Lemma measure_dec : forall (s: STV) (p c: Machine_States), 
    (initStep s p c) 
 \/ (count s p c) 
 \/ (elect s p c) 
 \/ (transfer_elected s p c) 
 \/ (transfer_removed s p c)  
 \/ (elim s p c) 
 \/ (hwin s p c) \/ (ewin s p c) -> 
    forall (ep : ~ State_final p) (ec: ~ State_final c), 
    Order_NatProduct (Measure_States (IsNonFinal c ec)) 
                     (Measure_States (IsNonFinal p ep)).   
Proof.
 intros s p c H ep ec.
 destruct H.
 apply (dec_Initial s p c H ep ec).
 destruct H.
 apply (dec_Count s p c H ep ec).
 destruct H.
 apply (dec_Elect s p c H ep ec).
 destruct H.
 apply (dec_TransferElected s p c H ep ec).
(* destruct H.
 apply (dec_TransferElected2 s p c H ep ec). *)
 destruct H.
 apply (dec_TransferRemoved s p c H ep ec).
 destruct H.
 apply (dec_Elim s p c H ep ec).
 destruct H.
 apply (dec_Hwin s p c H ep ec).
 apply (dec_Ewin s p c H ep ec).
Qed.

(*end of measure decreasing proof for new formalised rules*)
(* start: Certificate st bs s (state (Filter bs, [nty], nas, [], 
                                    emp_elec,all_hopeful)) *)


Inductive Certificate 
   (st: nat) (bs: list ballot) 
   (s: STV) (j0: Machine_States): Machine_States -> Type:=
  start:  
  forall j, (j = j0) -> Certificate st bs s j0 j
 |appInit: 
  forall j1 j2, Certificate st bs s j0 j1 -> initStep s j1 j2 
                 -> Certificate st bs s j0 j2 
 |appCount: 
  forall j1 j2, Certificate st bs s j0 j1 -> count s j1 j2 
                 -> Certificate st bs s j0 j2   
 |appElect: 
  forall j1 j2, Certificate st bs s j0 j1 -> elect s j1 j2 
                 -> Certificate st bs s j0 j2
 |appTransElected: 
  forall j1 j2, Certificate st bs s j0 j1 -> transfer_elected s j1 j2 
                 -> Certificate st bs s j0 j2
 |appTransRemoved: 
  forall j1 j2, Certificate st bs s j0 j1 -> transfer_removed s j1 j2 
                 -> Certificate st bs s j0 j2
 | appElim: 
  forall j1 j2, Certificate st bs s j0 j1 -> elim s j1 j2 
                 -> Certificate st bs s j0 j2 
 | appHwin: 
  forall j1 j2, Certificate st bs s j0 j1 -> hwin s j1 j2 
                 -> Certificate st bs s j0 j2
 | appEwin: 
  forall j1 j2, Certificate st bs s j0 j1 -> ewin s j1 j2 
                 -> Certificate st bs s j0 j2.

Lemma Rule_Application : forall (s: STV) (j1: Machine_States), ~ (State_final j1) -> 
   existsT j2, {initStep s j1 j2} + {count s j1 j2} + {elect s j1 j2} + {transfer_elected s j1 j2} + 
   {transfer_removed s j1 j2} + {elim s j1 j2} + {hwin s j1 j2} + {ewin s j1 j2}. 
Proof.
 intros s j1 H.
 destruct s.
 destruct j1.
 simpl.
 unfold SanityCheck_Initial_App in  evidence_applicability_initStep0. 
 specialize (evidence_applicability_initStep0  (initial l) l (eq_refl)).
 destruct evidence_applicability_initStep0 as [conc [H11 H12]].
 exists conc.
 left; left; left; left; left;left. auto.
 simpl.
 destruct p as [[[[[ba t] pile] bl] e] h].
 specialize (lt_eq_lt_dec (length (proj1_sig e)) X.st). intro LenElected.
 (* examining if we have filled all seats *)
 destruct LenElected as [LenElected1 | LenElected2]. 
 destruct LenElected1 as [LenElected11 | LenElected12].
 (* the case where there are seats to fill *)
 specialize (le_gt_dec (length (proj1_sig e) + length (proj1_sig h)) X.st). intro LenElectedHopeful.
 (* examining the length of elected and hopeful togather *)
 destruct LenElectedHopeful as [LenElectedHopeful1 | LenElectedHopeful2]. 
 (* the case where len (e ++ h) <= st *)
 (*destruct evidence_hwin0 as [HevHwin1 HevHwin2].*)
 unfold SanityCheck_Hwin_App in evidence_applicability_hwin0.
 specialize (evidence_applicability_hwin0 (state (ba, t, pile, bl, e, h)) ba t pile bl e h  (eq_refl) LenElectedHopeful1).
 destruct evidence_applicability_hwin0 as [conc HevHwin11]. 
 exists conc.
 left. right. assumption.
 (* the case where are more elected and hopeful than seats and less elected than seats*)
 destruct ba. 
 assert (([]<> (proj1_sig h)) -> 
       existsT d, In d (proj1_sig h) /\  (forall d', In d' (proj1_sig h) -> 
       ((hd nty t) d' <= (hd nty t) d)%Q)) by
           apply (list_max_cor X.cand (proj1_sig h) (hd nty t)).
 assert (forall (q:Q), ((forall c, In c (proj1_sig h) -> 
   ((hd nty t)(c) < q)%Q) + (existsT c: X.cand, In c (proj1_sig h) /\ ((hd nty t) (c) >= q)%Q))). 
 induction (proj1_sig h).
 intro q0.
 left; intros. contradict H0.
 assert (forall a: X.cand, forall h : list X.cand, [] <> a::h).
 intros.
 intro.
 inversion H0.
 specialize (X (H0 a l)).
 destruct X.
 destruct a0.
 assert (forall (q1: Q), (sumbool (((hd nty t) x < q1)%Q) ((q1 <= (hd nty t) x)%Q))).
 intro q1.
 apply (Qlt_le_dec ((hd nty t) x) q1).
 intro q2.
 specialize (H3 q2).
 destruct H3.
 left.
 intros.
 specialize (H2 c H3).
 apply (Qle_lt_trans ((hd nty t) c) ((hd nty t) x) q2).
 auto. auto.
 right.
 exists x.
 split; auto ; auto.
 specialize (X0 X.quota).
 destruct X0.
 destruct bl as [bl1 bl2].
 destruct bl1.
 assert ((proj1_sig h) <> []).
 specialize (list_min X.cand (proj1_sig h) (hd nty t)).
 intro.
 destruct X0.
 destruct (proj1_sig h).
 simpl in LenElectedHopeful2. 
 omega.
 inversion e0.
 destruct s.
 destruct a. 
 intro. rewrite H2 in H0. inversion H0.
 (* the case for elimination or transfer_removed*)
 destruct bl2.
 (* elimination *)
 unfold SanityCheck_Elim_App in evidence_applicability_elim0.
 specialize (evidence_applicability_elim0 (state ([], t, pile, ([], []), e, h)) t pile e h  (eq_refl)) .
 intuition. 
 destruct X0 as [conc Hconc].
 exists conc.
 left; left; right. auto.
 (* the case for transfer_removed *)
 unfold SanityCheck_TransferRemoved_App in evidence_applicability_transferRemoved0. 
 specialize (evidence_applicability_transferRemoved0 (state ([], t, pile,([],c::bl2),e, h)) t pile [] bl2 c e h (eq_refl)). 
 intuition.
 destruct X0 as [conc Hconc].
 exists conc.
 left; left; left; right. auto.
 (* the case of transfer *)
 unfold SanityCheck_TransferElected_App in evidence_applicability_transferElected0.
 (* here I pull the rabit out and destruct on the second component of backlog to take care of Victoria-elim*)
 destruct bl2.
 specialize (evidence_applicability_transferElected0 (state ([], t, pile, (c::bl1, []), e,h)) t pile (c::bl1, []) e h).
 simpl in evidence_applicability_transferElected0.
 intuition.
 assert (Hyp: (fst (c:: bl1, ([]: list X.cand))) = [] -> False). intro Hyp1. simpl in Hyp1. inversion Hyp1. 
 intuition.
 destruct X1 as [conc X31].
 exists conc. 
 left; left;left;left. right. assumption.
 (* the case where the snd of backlog is not empty, still in transfer phase*)
 (* the following part is commented out because of the change for transferRemoved *)
 (* assert (Hyz: sumbool (concat (pile c0) = []) (concat (pile c0) <> [])).
 destruct (concat (pile c0)). left;auto. right. intro.  inversion H0.
 destruct Hyz as [i | j].
 (* if the snd of backlog is empty then continue with the noraml transfer of elected votes *) 
 unfold SanityCheck_Transfer2_App in evidence_applicability_transfer2_elected0 . 
 specialize (evidence_applicability_transfer2_elected0 (state ([], t,pile, (c::bl1, c0:: bl2), e, h)) t pile 
                 (c::bl1) bl2 c0 e h (eq_refl)).
 simpl in evidence_applicability_transfer2_elected0.
 assert (auxTransHyp1: c::bl1 <> []). intro myhyp. inversion myhyp.
 intuition.
 destruct X0 as [conc X11].
 exists conc. 
 left;left;left; left. right. assumption. *)

 (* the case where still some ballots of the eliminated await transfer *)
 specialize (evidence_applicability_transferRemoved0 (state ([], t, pile, (c::bl1, c0::bl2), e, h)) t pile
                 (c::bl1) bl2 c0 e h (eq_refl)).
 simpl in evidence_applicability_transferRemoved0.
 assert (hypAux: c::bl1 <> []). intro myhyp. inversion myhyp.
 intuition.
 destruct X0 as [conc X11].
 exists conc.
 left; left; left; right. assumption.
 (* the case for electing *)
 unfold SanityCheck_Elect_App in evidence_applicability_elect0. 
 specialize (evidence_applicability_elect0 (state ([], t, pile, bl, e, h)) t pile bl e h (eq_refl)).
 destruct s as [c s1].
 assert (HypE2: existsT c, (length (proj1_sig e)) + 1 <= X.st /\ (In c (proj1_sig h)) 
                                                           /\ (X.quota <= (hd nty t) c)%Q). 
 exists c.
 split. omega. 
 auto.
 specialize (evidence_applicability_elect0 HypE2).
 destruct evidence_applicability_elect0 as [conc HevElect21]. 
 exists conc.
 left; left; left; left; left; right. assumption.
 (* the case for count application *)
 unfold SanityCheck_Count_App in evidence_applicability_count0.  
 specialize (evidence_applicability_count0 (state (b ::ba, t, pile, bl, e, h)) (b::ba) t pile bl h e (eq_refl)).
 assert (HyCount: (b:: ba) <> []). intro. inversion H0.
 specialize (evidence_applicability_count0 HyCount). 
 destruct evidence_applicability_count0 as [conc HevCount].
 exists conc.
 left; left; left; left; left; left; right. auto.
 (* the case for ewin *)
 unfold SanityCheck_Ewin_App in evidence_applicability_ewin0.
 specialize (evidence_applicability_ewin0 (state (ba, t, pile, bl, e, h)) ba t pile bl e h  (eq_refl)). 
 intuition.
 destruct X as [conc X1]. 
 exists conc.
 right. assumption.
 (* the impossible case where len e > st *)
 destruct e as [e0 e1].
 simpl in LenElected2.
 omega.
 simpl.
 contradict H. exists l. reflexivity.
Qed.

Lemma Extending_Certificate : forall (bs: list ballot), 
  forall (s: STV),
  forall j0 j1, forall (ej0: ~ State_final j0) (ej1: ~ State_final j1), Certificate X.st bs s j0 j1 ->
    existsT j2, 
        (Certificate X.st bs s j0 j2) * 
        (forall ej2: (~ State_final j2), Order_NatProduct (Measure_States (IsNonFinal j2 ej2)) (Measure_States (IsNonFinal j1 ej1))).                     
Proof.
 intros bs s j0 j1 ej0 ej1 H0.
 specialize (Rule_Application s j1 ej1). intro H1.
 destruct H1 as [conc H11].
 destruct H11 as [LH11 | RH11]. 
 destruct LH11 as [LLH11 | RLH11].
 destruct LLH11 as [LLLH11 | RLLH11]. 
 destruct LLLH11 as [LLLLH11 | RLLLH11].
 destruct LLLLH11 as [LLLLLH11 | RLLLLH11].
 destruct LLLLLH11 as [L6H11 | RL5H11].
 destruct L6H11 as [L7H11 |L7H12].
 (*destruct L7H11 as [L8H11 | L8H12]. *)
 exists conc.
 split.
 apply (appInit X.st bs s j0 j1). assumption. auto.
 intro evconc. 
 apply (dec_Initial s j1 conc L7H11). 
 exists conc. 
 split.
 apply (appCount X.st bs s j0 j1). assumption. auto.
 apply (dec_Count s j1 conc L7H12).
 exists conc.
 split.
 apply (appElect X.st bs s j0 j1). assumption. auto.
 apply (dec_Elect s j1 conc RL5H11). 
 exists conc. 
 split. 
 apply (appTransElected X.st bs s j0 j1).  assumption. auto.
 apply (dec_TransferElected s j1 conc RLLLLH11).
 exists conc.
 split.
(* apply (appTrans2 X.st bs s j0 j1). assumption. auto.
 apply (dec_TransferElected2 s j1 conc RLLLLH11).
 exists conc.
 split. *)
 apply (appTransRemoved X.st bs s j0 j1). assumption. auto.
 apply (dec_TransferRemoved s j1 conc RLLLH11).
 exists conc.
 split.
 apply (appElim X.st bs s j0 j1). assumption. auto.
 apply (dec_Elim s j1 conc RLLH11). 
 exists conc.
 split.
 apply (appHwin X.st bs s j0 j1). assumption. auto.
 apply (dec_Hwin s j1 conc RLH11).
 exists conc.
 split.
 apply (appEwin X.st bs s j0 j1). assumption. auto.
 apply (dec_Ewin s j1 conc RH11). 
Qed.

Lemma Termination_Aux : forall (bs: list ballot),
  forall (s: STV), 
  forall n: Product_Five_NatSet, 
  forall j0 (evj0: ~ State_final j0),
  forall j (evj: not (State_final j)), Measure_States (IsNonFinal j evj) = n -> 
        Certificate X.st bs s j0 j -> 
           existsT j', (State_final j') * (Certificate X.st bs s j0 j').
Proof.                                                
 intros bs s n j0 evj0. 
 induction n as [w IH] using (well_founded_induction_type Order_NatProduct_wf).
 intros j evj Eqn Certj.
 assert (Hex: existsT j', 
   (Certificate X.st bs s j0 j') * 
   (forall evj' : not (State_final j'), Order_NatProduct (Measure_States (IsNonFinal j' evj')) (Measure_States (IsNonFinal j evj)))).  
 apply (Extending_Certificate bs s j0 j evj0 evj Certj). 
 destruct Hex as [j' [Hex1 Hex2]].
 destruct (final_dec j') as [f | nf].
 exists j'. split. assumption. auto.
 specialize (Hex2 nf).
 rewrite <- Eqn in IH.
 destruct (IH (Measure_States (IsNonFinal j' nf)) Hex2 j' nf) as [j'' Hj''].
 reflexivity.  
 assumption.
 exists j''.
 auto.
Qed.

Theorem Termination : forall (bs: list ballot),
forall j0 (evj0: ~State_final j0), forall (s: STV), 
                            existsT j, (State_final j) * (Certificate X.st bs s j0 j).
Proof.
 intros bs j0 evj0 s.
 destruct (final_dec j0) as [f | ea].
 (*destruct (final_dec (state (Filter bs, [nty], nas, [], 
                                    emp_elec,all_hopeful))) as [f | ea].*)
 (*exists (state (Filter bs, [nty], nas, [], 
                                    emp_elec,all_hopeful)). *)
 contradict evj0.
 assumption.
 apply (Termination_Aux bs s (Measure_States (IsNonFinal j0 ea)) j0 ea j0 ea).  
 reflexivity.
 apply start. auto.
Qed. 

(*End Generic_Machine.*)

(*Section Base_Proofs.*)

(* relation for `first continuing candidate' on a ballot in the list of ballots requiring attention *)
Definition fcc (ba : list ballot) (h : list X.cand) (c : X.cand) (b : ballot): Prop := 
  In (proj1_sig (fst b)) ((map (fun (d: ballot) => (proj1_sig (fst d)))) ba) /\
  In c h /\
  (exists l1 l2 : list X.cand, 
      proj1_sig (fst b) = l1 ++ [c] ++ l2 /\ 
      forall d, (In d l1 -> ~(In d h))).

(*checks if no cadidate whose name is in h, does not precede the candidate c in the list l*)
Fixpoint is_first_hopeful (c: X.cand) (h: list X.cand) (l : list X.cand):=
 match l with
          [] => false
          |l0::ls =>  if (X.cand_in_dec c h) then
                                               if X.cand_eq_dec l0 c then true 
                                               else                     
                                                   if X.cand_in_dec l0 h then false
                                                   else is_first_hopeful c h ls
                      else false  
 end. 



(*collects all of the ballots where c is the first continuing preference*)
Fixpoint list_is_first_hopeful (c: X.cand) (h: list X.cand) (ba: list ballot):=
 match ba with
          [] => []
          |b0::bas => if (is_first_hopeful c h (proj1_sig (fst b0))) 
                         then b0::(list_is_first_hopeful c h bas)
                      else (list_is_first_hopeful c h bas)        
 end.

Fixpoint List_IsFirst_Hopeful (c: X.cand) (h :list X.cand) (acc: list ballot) (ba: list ballot) :=
 match ba with
         [] => acc
        |b0 :: bas => if is_first_hopeful c h (proj1_sig (fst b0))
                        then List_IsFirst_Hopeful c h (b0 :: acc) bas
                      else List_IsFirst_Hopeful c h acc bas
 end.

(*every ballot b which c is its first preference, is an elements of the uncounted ballots ba, so that ballots are not assigned to a cadidate from an illegal source*) 
Lemma weakened_is_first_hopeful_ballot: forall c h ba, forall (d: ballot), In (proj1_sig (fst d)) (map (fun (d0: ballot) => (proj1_sig (fst (d0)))) (list_is_first_hopeful c h ba)) -> In (proj1_sig (fst d)) (map (fun (d: ballot) => (proj1_sig (fst d))) ba).
Proof.
 intros.
 induction ba.
 simpl in H.
 inversion H.
 specialize (list_eq_dec (X.cand_eq_dec) (proj1_sig (fst d)) (proj1_sig (fst a))).
 intro H'1.
 destruct H'1 as [e |n].
 rewrite e.
 simpl.
 left;auto.
 simpl in H.
 simpl.
 right.
 apply IHba.
 destruct is_first_hopeful.
 simpl in H.
 destruct H as [Hi |Hj].
 rewrite Hi in n.
 contradiction n;reflexivity.
 assumption.
 auto.
Qed.

Lemma nonempty_list_notempty: forall l1 l2 (c: X.cand), [] <> l1++[c]++l2.
Proof.
 intros l1' l2' c'.   
 intro H'.       
 induction l1'.
 simpl in H'.
 inversion H'.
 rewrite <- (app_comm_cons) in H'.       
 inversion H'.
Qed.


(*if c is not the first continuing candidate in a ballot, then he does not receive that vote*) 
Lemma first_hopeful_false: forall c h d0 l1 l2, In d0 l1 -> In d0 h -> NoDup (l1++[c]++l2) -> is_first_hopeful c h (l1++[c]++l2) = false.
Proof.
 intros c h d0 l1 l2 H1 H2 H3.
 induction l1.
 simpl.
 inversion H1.
 destruct (X.cand_eq_dec d0 a).
 simpl.
 destruct (X.cand_in_dec c h) as [CandInDec1 |CandInDec2].
 destruct (X.cand_eq_dec a c) as [i | j].
 rewrite i in H3.
 inversion H3.
 assert (Hypo: In c (l1++c::l2)).
 intuition.
 contradiction H4.
 destruct (X.cand_in_dec a h) as [p |q].
 auto.
 rewrite e in H2.
 contradiction q.  auto.
 simpl.
 destruct (X.cand_in_dec c h) as [CandInDec1 | CandInDec2].
 destruct (X.cand_eq_dec a c) as [i' | j'].
 rewrite i' in H3.
 inversion H3.
 exfalso.
 apply H4.
 intuition.
 destruct (X.cand_in_dec a h) as [p' |q'].
 auto.
 apply IHl1.
 destruct H1 as [H11 |H12].
 contradiction n;symmetry;auto.
 assumption.
 inversion H3.
 simpl;assumption.
 reflexivity.
Qed.

(*if c is the first continuing candidate of a ballot, then he gets that vote*)
Lemma first_hopeful_true: forall c (h: {hopeful: list X.cand | NoDup hopeful}) (b: ballot) (ba: list ballot) l1 l2,(forall d, In d l1 -> ~ In d (proj1_sig h)) /\ (exists (d: ballot), (proj1_sig (fst d)) = l1++[c]++l2) /\ (In c (proj1_sig h)) -> is_first_hopeful c (proj1_sig h) (l1++[c]++l2) = true.
Proof.
 intros c h b ba l1 l2 H1.
 destruct H1 as [H11 [H12 H13]].
 assert (Hypo: NoDup (l1++[c]++l2) /\ ( []<> l1++[c]++l2)).
 destruct H12 as [d H121].
 destruct d as [[b1 [b121 b122]] b2]. 
 simpl in H121.
 split.
 simpl.
 rewrite <- H121.
 assumption.
 intro H3.
 simpl in H3.
 rewrite <- H121 in H3.
 apply b122.
 assumption.
 destruct Hypo as [Hypo1 Hypo2].
 induction l1.
 simpl.
 destruct (X.cand_in_dec c (proj1_sig h)) as [CandInDec1 | CandInDec2].
 destruct (X.cand_eq_dec c c) as [i1 |i2].
 auto.
 contradiction i2.
 auto.
 contradiction CandInDec2.
 simpl.
 destruct (X.cand_in_dec c (proj1_sig h) ) as [CandInDec3 | CandInDec4].
 destruct (X.cand_in_dec a (proj1_sig h)).
 specialize (H11 a).
 assert (Hypo: In a (a::l1)).
 left;auto.
 specialize (H11 Hypo).
 contradiction H11.
 destruct (X.cand_eq_dec a c) as [CandEqDec1 |CandEqDec2].
 reflexivity.
 apply IHl1.
 intros d0 H2.
 specialize (H11 d0).
 apply H11.
 right;assumption.
 specialize (nonempty_list_notempty l1 l2 c);intro Hypo5.
 assert (Hypo4: NoDup (l1++[c]++l2) /\ ([] <> l1++[c]++l2)).
 inversion Hypo1.
 split;simpl.
 assumption.
 intro H5.
 contradiction Hypo5.
 exists ((exist (fun v => NoDup v /\ ([] <> v)) (l1++[c]++l2) Hypo4), (1)%Q).
 simpl.
 auto.
 inversion Hypo1.
 simpl;assumption.
 specialize (nonempty_list_notempty l1 l2 c);intro Hypo6;auto.            
 contradiction CandInDec4.
Qed.

(*c receives all of the ballots that prefer him as their first contiuing choice*)
Lemma fcc_listballot: forall ba (h: {hopeful: list X.cand | NoDup hopeful}),(forall c, forall d: ballot,  fcc ba (proj1_sig h) c d -> In (proj1_sig (fst d)) (map (fun (d0:ballot) => (proj1_sig (fst d0))) (list_is_first_hopeful c (proj1_sig h) ba))).
Proof.
 intros ba h c.
 intros d H4.
 unfold fcc in H4.
 destruct H4 as [H4_1 [H4_2 [l1 [l2 [H4_3 H4_4]]]]].
 induction ba.
 inversion H4_1.
 simpl.
 specialize (list_eq_dec (X.cand_eq_dec) (proj1_sig (fst d)) (proj1_sig (fst a))).
 intro H'.
 destruct H' as [i |j ].
 rewrite<- i.
 rewrite H4_3.
 rewrite (first_hopeful_true c h d ba l1 l2).
 left;auto.
 rewrite<- i.
 assumption.
 split.
 auto.
 split.
 exists d. assumption. assumption.
 destruct (is_first_hopeful).
 right.
 apply IHba.
 destruct H4_1.
 contradiction j.
 auto. 
 assumption.
 apply IHba.
 destruct H4_1.
 contradiction j.
 auto.
 assumption.
Qed.

(*if c is not a continuing candidate, he does not receive any vote any more*)
Lemma is_first_hopeful_In: forall (c:X.cand) h l, is_first_hopeful c h l =true -> In c l.
Proof.
 intros c h l H1.
 induction l.
 simpl in H1.
 inversion H1.
 destruct (X.cand_in_dec a h) as [i1 | i2].
 unfold is_first_hopeful in H1.
 destruct (X.cand_in_dec c h) as [p1 |p2].
 destruct (X.cand_eq_dec a c) as [j1 |j2].
 left;assumption.
 destruct (X.cand_in_dec a h) as [s1 |s2].
 inversion H1.
 contradiction s2.
 right.
 apply IHl.
 inversion H1.
 right.
 apply IHl. 
 assert (Hypo: is_first_hopeful c h (a::l) = is_first_hopeful c h l).
 induction l.
 unfold is_first_hopeful in H1.
 destruct (X.cand_in_dec) as [CandInDec1 | CandInDec2].
 destruct (X.cand_eq_dec a c) as [CandEqDec1 |CandEqDec2].
 rewrite  CandEqDec1 in i2.
 contradiction i2.
 destruct (X.cand_in_dec a h) as [CandInDec3 | CandInDec4].
 contradiction i2.
 inversion H1.
 inversion H1.
 simpl.
 destruct (X.cand_in_dec c h) as [p1 |p2].
 destruct (X.cand_eq_dec a c ) as [p3 |p4].
 rewrite p3 in i2.
 contradiction i2.
 destruct (X.cand_in_dec a h) as [p5 |p6].
 contradiction i2.
 destruct (X.cand_eq_dec a0 c) as [p7 |p8].
 reflexivity.
 destruct (X.cand_in_dec a0 h) as [p9 |p10].
 reflexivity.
 reflexivity.
 reflexivity.
 rewrite <- Hypo.
 assumption.
Qed.

Lemma list_is_first_hopeful_In: forall (ba: list ballot) (b:ballot) (h: {hopeful:list X.cand | NoDup hopeful}) (c:X.cand),  In (proj1_sig (fst b)) (map (fun (d:ballot) => (proj1_sig (fst d))) (list_is_first_hopeful c (proj1_sig h) ba)) -> In c (proj1_sig (fst b)). 
Proof.
 intros ba b h c H1.
 unfold list_is_first_hopeful in H1.
 induction ba.
 simpl in H1.
 exfalso.
 assumption.
 simpl in H1.
 specialize (is_first_hopeful_In c (proj1_sig h) (proj1_sig (fst a)));intro H2.
 destruct is_first_hopeful.
 simpl in H1.
 destruct H1.
 rewrite <- H.
 apply H2.
 reflexivity.
 apply IHba. 
 auto.
 apply IHba.
 assumption.
Qed.

(*all the ballots which have already been filtered have no duplicate*)
Lemma ballot_nodup: forall (ba: list ballot) (t : list (X.cand ->Q)) (p: X.cand -> list (list ballot)) bl (e: {elected: list X.cand | length elected <= X.st}) (h: {hopeful : list X.cand | NoDup hopeful}) s,s= state (ba, t, p, bl, e, h) -> forall b: ballot, NoDup (proj1_sig (fst b)).
Proof.
 intros ba t p bl e h  s H1 b.
 destruct b as [[b11 [b121 b122]] b2].
 simpl.
  assumption.
Qed.


(*if c is not the first continuing candidate in a ballot then c does not receives it*)
Lemma weakened_list_is_first_notin: forall (t: list (X.cand -> Q)) (e: {elected:list X.cand| length elected <= X.st}) (p: X.cand -> list (list ballot)) (bl: (list X.cand) * (list X.cand)) c (h: {hopeful: list X.cand | NoDup hopeful}) (n:Q) ba (d:ballot) (d0:X.cand) l1 l2, proj1_sig (fst d)= l1++[c]++l2 -> In d0 l1 -> In d0 (proj1_sig h) -> ~ In (proj1_sig (fst d)) (map (fun (d' :ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba)).
Proof.
 intros t e p bl c h n ba d d0 l1 l2 H1 H2 H3.
 induction ba.
 simpl.
 intro.
 auto.
 intro H4.
 specialize (list_eq_dec (X.cand_eq_dec) (proj1_sig (fst (d))) (proj1_sig (fst a))).
 intro H'.       
 simpl in H4.
 destruct H' as [h' |h''].
 rewrite<-  h' in H4.
 rewrite H1 in H4.
 rewrite (first_hopeful_false c (proj1_sig h) d0 l1 l2) in H4.
 rewrite <- H1 in H4.        
 contradiction IHba.
 assumption.
 assumption.
 rewrite <- H1.
 apply (ballot_nodup ba t p bl e h (state (ba, t, p, bl, e, h))).
 reflexivity.
 destruct (is_first_hopeful).
 destruct H4.
 destruct a.
 destruct d.
 rewrite H in h''.
 contradiction h''.
 auto.
 contradiction IHba.
 contradiction IHba.
Qed.

(*c gets exactly those ballots which have him as their first continuing candidate*)
Lemma listballot_fcc: forall ba (t: list (X.cand -> Q)) (p: X.cand -> list (list ballot)) (bl: (list X.cand) * (list X.cand)) (e: {elected: list X.cand | length elected <= X.st}) (h: {hopeful: list X.cand | NoDup hopeful}) (n:Q), (forall c, In c (proj1_sig h) -> forall d: ballot, In (proj1_sig (fst d)) (map (fun (d':ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba)) <-> fcc ba (proj1_sig h) c d).
Proof.
 intros ba t p bl e h n.
 intros c H3.
 split.
 intro H4.
 unfold fcc.
 split.
 apply (weakened_is_first_hopeful_ballot  c (proj1_sig h) ba).
 assumption.
 split.
 assumption.
 assert (Hypo: In c (proj1_sig (fst d))).
 apply (list_is_first_hopeful_In ba d h c H4).
 specialize (in_split c (proj1_sig (fst d)) Hypo);intro H5.
 destruct H5 as [l1 [l2 H5_2]].
 exists l1.
 exists l2.
 split.
 auto.
 intros d0 H6.
 intro H7.
 assert (Hypo2: ~ In (proj1_sig (fst d)) (map (fun (d' :ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba))). 
 apply (weakened_list_is_first_notin t e p bl c h n ba d d0 l1 l2 H5_2 H6 H7).
 contradiction Hypo2.
 intro H4.
 specialize (fcc_listballot ba h c d H4);intro H5.
 assumption.
Qed.

Lemma list_nonempty: forall (A: Type) (l: list A), [] = l \/ exists b l', l= b::l'.
Proof.
 intros A l.
 induction l.
 left.
 auto.
 destruct IHl as [i | j].
 right.
 exists a.
 exists ([]: list A).
 rewrite <- i.
 auto.
 destruct j as [b [l' H1]].
 right.
 exists a.
 exists (b::l').
 rewrite H1.
 reflexivity.
Qed.

Lemma list_nonempty_type: forall (A: Type) (l : list A), l <> [] -> existsT b l', l = b :: l'.
Proof.
 intros A l H.
 specialize (destruct_list l). intro.
 destruct X.
 destruct s.
 destruct s. 
 exists x.
 exists x0.
 auto.
 contradict H. assumption.
Qed.

Definition eqe {A: Type} (x:A) (l: list A) (nl: list A) : Prop :=
 exists l1 l2: list A, 
  l = l1 ++ l2 /\ 
  nl = l1 ++ [x] ++ l2 /\ 
  (~ In x l1) /\ 
  (~ In x l2).

Fixpoint remc (c: X.cand) (l: list X.cand) :=
 match l with 
    nil => nil
   | cons l0 ls => if (X.cand_eq_dec c l0) then ls else cons l0 (remc c ls)
 end.

Lemma remc_ok : forall c:X.cand, forall l:list X.cand, NoDup l -> In c l -> eqe c (remc c l) l.
Proof.
 intros c l H1 H2.  
 induction l.
 inversion H2.
 assert (H3: {a =c} + {a <> c}) by apply (X.cand_eq_dec a c).
 destruct H3 as [H4 | H4].
 replace (remc c (a::l)) with l. 
 unfold eqe.
 exists ([]:list X.cand).
 exists l.
 split.
 auto.
 split.
 rewrite H4.
 auto.
 split.
 intro H5.
 inversion H5.
 intro H5.
 inversion H1.
 rewrite<-  H4 in H5.
 intuition.
 rewrite H4.
 unfold remc.
 destruct (X.cand_eq_dec c c).
 reflexivity.
 contradiction n.
 auto.
 inversion H1.
 destruct H0 as [H5 H6].
 assert (H7: a =c \/ In c l0) by apply (in_inv H2).
 destruct H7 as [H8 | H8].
 contradiction H4.
 assert (H9: (eqe c (remc c l0) l0 )) by apply (IHl H5 H8).
 replace (remc c (a::l0))  with (a::(remc c l0)).
 unfold eqe in H9.
 destruct H9 as [l1 H10].
 destruct H10 as [l2 H11].
 destruct H11 as [H12 [H13 H14]].
 unfold eqe.
 exists (a::l1).
 exists l2.
 split.
 simpl.
 rewrite H12.
 auto.
 split.
 simpl.
 rewrite H13.
 reflexivity.
 split.
 destruct H14 as [H15 H16].
 intro H17.
 destruct H17 as [H18 |H18].
 contradiction H4.
 contradiction H15.
 destruct H14 as [H15 H16].
 assumption.
 unfold remc.
 destruct (X.cand_eq_dec c a).
 contradict H4.
 symmetry.
 assumption.
 trivial.
Qed.

Lemma remc_contained_in_list: forall (l: list X.cand) c a, NoDup l -> In a (remc c l) -> In a l.
Proof.
 intros l c a H H1.
 induction l.
 simpl in H1.
 inversion H1.
 destruct (X.cand_eq_dec c a0) as [p |q].
 rewrite p in H1.
 simpl in H1.
 destruct (X.cand_eq_dec a0 a0) as [p1 | p2].
 right;assumption.
 contradiction p2;auto.
 assert (Hypo: (remc c (a0::l))= (a0::remc c l)).
 simpl.
 destruct (X.cand_eq_dec c a0) as [i | j].
 contradiction q.
 reflexivity.
 rewrite Hypo in H1.
 destruct H1 as [H1_1 | H1_2].
 left;assumption.
 right.
 apply IHl.
 inversion H.
 assumption.
 assumption.
Qed.

Lemma remc_nodup : forall (l : list X.cand) c, NoDup l -> In c l -> NoDup (remc c l).
Proof.
 intros l c H1 H2.
 induction l.
 inversion H2.
 destruct (X.cand_eq_dec c a) as [i |j].
 rewrite i.
 simpl.
 destruct (X.cand_eq_dec a a) as [ p |q].
 inversion H1.
 assumption.
 contradiction q;auto.
 replace (remc c (a::l)) with (a::remc c l).
 apply NoDup_cons.
 destruct H2 as [H2_1| H2_2].
 contradiction j.
 auto.
 inversion H1.
 intro H4.
 apply H2.
 apply (remc_contained_in_list l c a H3 H4).
 apply IHl.
 inversion H1.
 assumption.
 destruct H2 as [H2_1 |H2_2].
 contradiction j.
 auto.
 assumption.
 simpl.
 destruct (X.cand_eq_dec c a).
 contradiction j;auto.
 reflexivity.
Qed.

Inductive ordered {A : Type} (f : A -> Q) : list A -> Prop := 
  ord_emp : ordered f []  
 | ord_sing : forall x : A, ordered f [x]
 | ord_cons : forall l x y, ordered f (y :: l) -> (f(x) >= f(y))%Q -> ordered f (x :: y :: l).

Definition Leqe {A:Type} (k :list A) (l: list A) (nl: list A): Prop:=
 Permutation nl (l++k).

Lemma ordered_head: forall (A: Type) (x y:A) r f, ordered f (x::y::r) -> (f x >= f y)%Q.
Proof.
 intros.
 inversion H.
 auto.
Qed.

(*if a list is ordered w.r.t. function f, then its tail is also ordered w.r.t.*)
Lemma ordered_tl: forall (A:Type)(a:A) f l, ordered f (a::l) -> ordered f l.
Proof.
 intros A a f l H0.
 inversion H0.
 apply ord_emp.
 auto.
Qed.

Lemma ordered_is_ordered: forall (A:Type) f (a b:A) l l'', (forall l', ordered f (l++[a]++l'++[b]++l'')) -> (f b <= f a)%Q.
Proof.
 intros.
 induction l.
 specialize (H ([]:list A)).
 simpl in H.
 apply (ordered_head A a b l'' f) in H.
 auto.
 apply IHl.
 intro.
 specialize (H l').
 rewrite<- app_comm_cons in H.
 apply (ordered_tl A a0 f (l++[a]++l'++[b]++l'')).
 auto.
Qed.

Lemma ordered_head_greatest: forall A:Type, forall f, forall a, forall b:A, forall l', (forall l,ordered f (a::(l++[b]++l')) )-> ( f b <= f a)%Q.
Proof.
 intros.
 specialize (ordered_is_ordered A f a b [] l').
 intros.
 apply H0.
 simpl.
 auto.
Qed.

Lemma ordered_head_rep: forall (A:Type) f (l:list A) (a b:A), ordered f (a::l) -> (f a <= f b)%Q -> ordered f (b::l).
Proof.
 intros.
 induction l.
 apply ord_sing.
 apply ord_cons.
 specialize (ordered_tl A a f (a0::l) H);intro.
 auto.
 apply (Qle_trans ( f a0) (f a) (f b)).
 apply (ordered_head A a a0 l f).
 auto.
 auto.
Qed.

(*if a list is ordered w.r.t. f, then if one removes any segment ffrom it, the remainder list is ordered still.*) 
Lemma ordered_remove: forall (A:Type) f (l:list A) l' (a b:A), ordered f (a::l++[b]++l') -> ordered f (a::b::l').
Proof.
 intros.
 induction l.
 auto.
 apply IHl.
 inversion H. 
 apply (ordered_head_rep A f (l++[b]++l') a0 a H2).
 auto.
Qed.

(* if a list is ordered w.r.t. function f, given a new element a, one can always insert a into the list without destroying the order.*)
Lemma extend_ordered_type: forall A:Type, forall f: A -> Q, forall x: list A, ordered f x -> (forall a:A, (existsT y z, x =y++z /\ ordered f (y++[a]++z))).
Proof.
 intros A f x H1 a.
 induction x.
 exists ([]: list A).
 exists ([]: list A).
 split.
 auto.
 apply ord_sing.
 destruct IHx.
 apply (ordered_tl A a0 f x).
 auto.
 destruct s as [z H2].
 destruct H2 as [H5 H6].
 assert (Hyp: sumbool ((f a0 < f a)%Q) ((f a <= f a0)%Q)) by apply (Qlt_le_dec (f a0)(f a)).
 destruct Hyp as [Hyp1 | Hyp2].
 destruct x0.
 simpl in H6.
 simpl in H5.
 rewrite H5 in H1.
 exists ([]: list A).
 exists (a0::z).
 repeat split.
 rewrite H5;auto.
 simpl.
 apply (Qlt_le_weak (f a0) (f a)) in Hyp1.
 apply ord_cons.
 auto.
 auto.
 rewrite H5 in H1.
 rewrite <- app_comm_cons in H1.
 specialize (ordered_head A a0 a1 (x0++z) f H1);intro.
 rewrite <- app_comm_cons in H6.
 specialize (ordered_head_greatest A f a1 a z).
 intro.
 specialize (ordered_remove A f x0 z a1 a H6);intro.
 specialize (ordered_head A a1 a z f H2);intro H11.
 specialize (Qlt_not_le (f a0) (f a) Hyp1);intro.
 specialize (Qle_trans (f a) (f a1) (f a0) H11 H);intro.
 contradiction.
 exists (a0::x0).
 exists z.
 rewrite H5.
 repeat split.
 induction x0.
 apply ord_cons.
 auto.
 assumption.
 rewrite H5 in H1.
 rewrite<- (app_comm_cons (a1::x0) ([a]++z) a0).
 apply (ord_cons f (x0++[a]++z) a0 a1).
 auto.
 specialize (ordered_head A a0 a1 (x0++z) f H1);intro.
 auto.
Qed.

(*if a list has no duplication, then adding elements which were not in it does not creat duplication.*)
Lemma NoDup_middle: forall (a:X.cand) m1 m2, ~ In a (m1++m2) -> NoDup (m1++m2) -> NoDup (m1++[a]++m2).
Proof.
 intros a m1 m2 H1 H2.
 induction m1.
 apply NoDup_cons.
 auto.
 assumption.
 rewrite <-app_comm_cons .
 apply NoDup_cons.
 rewrite <- app_comm_cons in H2.
 inversion H2.
 intro h.
 apply H3.
 specialize (in_app_or m1 ([a]++m2) a0 h);intro h1.
 destruct h1 as [h2 | h3].
 intuition.
 destruct h3 as [h4 | h5].
 rewrite h4 in H1.
 destruct H1.
 left;auto.
 intuition.
 apply IHm1.
 intro h.
 apply H1.
 rewrite <- app_comm_cons.
 right.
 assumption.
 rewrite <- app_comm_cons in H2.
 inversion H2.
 assumption.
Qed.

(*if there are vacancies, we can construct a list electable candidates who have reached the quota. Besides this list is orderedw.r.t. tally, and it contains all of such electable candidates.*)
Lemma constructing_electable_first: forall (e: {elected:list X.cand | length elected <= X.st}) (f: X.cand -> Q) (h: {hopeful: list X.cand | NoDup hopeful}) (qu:Q), X.st > length (proj1_sig e) -> NoDup (proj1_sig h) -> (existsT m, (forall x: X.cand, In x m -> In x (proj1_sig h) /\ (qu <= f x)%Q) /\ (ordered f m) /\ NoDup m /\ (length m <= X.st - (length (proj1_sig e))) /\ (forall x, In x (proj1_sig h) /\ (qu <= f x)%Q /\ length m < X.st - length (proj1_sig e) -> In x m)). 
Proof.
 intros e f h qu H H1. 
 induction (proj1_sig h).
 exists ([]:list X.cand).
 split.
 intros x H2.
 inversion H2. 
 split.
 apply ord_emp.
 split.
 assumption.
 split.
 simpl.
 omega.
 intros x H2.
 destruct H2 as [H2_1 H2_2].
 inversion H2_1.
 specialize (NoDup_remove_1 [] l a H1);intro H2.
 simpl in H2.
 assert (Hyp1: sumbool ((f a < qu)%Q) ((qu <= f a)%Q)) by apply (Qlt_le_dec (f a) qu).
 destruct Hyp1 as [Hyp1_1 | Hyp1_2].
 specialize (IHl H2).
 destruct IHl as [m H3].
 destruct H3 as [H3_1[ H3_2 H3_3 ]].
 destruct (X.cand_in_dec a m) as [i | j].
 specialize (H3_1 a i).
 destruct H3_1 as [H3_11 H3_12].
 specialize (Qlt_not_le (f a) qu Hyp1_1);intros H3_4.
 contradiction H3_4.
 exists m.
 split.
 intros x H4.
 split.
 destruct (X.cand_eq_dec a x) as [p | q].
 rewrite p in j.
 contradiction j.
 right.
 specialize (H3_1 x H4).
 intuition.
 specialize (H3_1 x H4).
 intuition.
 split.
 assumption.
 split.
 intuition.
 split.
 intuition.
 intros x H4.
 apply H3_3.
 destruct H4 as [H4_1 [H4_2 H4_3]].
 destruct H4_1 as [H4_11 | H4_12].
 rewrite H4_11 in Hyp1_1.
 specialize (Qlt_not_le (f x) qu Hyp1_1);intro H5.
 contradiction H5.                       
 repeat split;assumption.
 specialize (IHl H2).
 destruct IHl as [m H3].
 destruct H3 as [H3_1 [H3_2 H3_3]].
 destruct (X.cand_in_dec a m) as [i | j].
 specialize (H3_1 a i).
 destruct H3_1 as [H3_11 H3_12].
 specialize (NoDup_remove_2 [] l a H1);intros H5.
 contradiction H5.
 destruct H3_3 as [H3_31 [H3_32 H3_4]].
 specialize (le_lt_eq_dec (length m) (X.st - length (proj1_sig e)) H3_32);intro H3_33.
 destruct H3_33 as [H3_331 | H3_332].
 specialize (extend_ordered_type X.cand (f: X.cand -> Q) m H3_2 a);intro H4.
 destruct H4 as [m1 [m2 H4_1]].
 destruct H4_1 as [H4_5 H4_6].
 exists (m1++[a] ++m2).
 split.
 intros x H5.
 split.
 specialize (in_app_or m1 ([a]++m2) x H5);intro H6.
 destruct H6 as [H6_1 | H6_2].
 assert (Hyp2: In x m).
 rewrite H4_5.
 intuition.
 specialize (H3_1 x Hyp2).
 right.
 intuition.
 destruct H6_2 as [H6_3 | H6_4].
 left.
 assumption.
 right.
 assert (Hyp3: In x m).
 rewrite H4_5.
 intuition.
 specialize (H3_1 x).
 intuition.
 specialize (H3_1 x).
 destruct (X.cand_eq_dec a x) as [p |q].
 rewrite p in Hyp1_2.
 assumption.
 assert (Hyp4: In x m).
 specialize (in_app_or m1 ([a]++m2) x H5);intro H6.
 destruct H6 as [H6_1 | H6_2].
 rewrite H4_5.
 intuition.
 destruct H6_2 as [H6_3 | H6_4].
 contradiction q.
 rewrite H4_5.
 intuition.
 intuition.
 split.
 assumption.
 split.
 apply (NoDup_middle a m1 m2).
 rewrite H4_5 in j.
 assumption.
 rewrite <- H4_5.
 intuition.
 split.
 rewrite app_length.
 simpl.
 rewrite H4_5 in H3_331.
 rewrite app_length in H3_331.
 omega.
 intros x H5.
 destruct (X.cand_eq_dec a x) as [p | q].
 rewrite p.
 intuition.
 destruct H5 as [H5_1 [H5_2 H5_3]].
 destruct H5_1 as [H5_11 | H5_12].
 contradiction q.
 specialize (H3_4 x).
 intuition.
 rewrite H4_5 in H0.
 specialize (in_app_or m1 m2 x H0);intro H6.
 destruct H6 as [H6_1 | H6_2].
 apply (in_or_app).
 left;assumption.
 intuition.
 (* this is when a is over the quota but already we have filled all of the vacancies *)
 (* so I will simply ignore that a is electable. If a tie has occurred essentially the one preceding a wins *)
 exists m.
 split. 
 intros x H4.
 split.
 right.
 specialize (H3_1 x).
 intuition.  
 specialize (H3_1 x).
 intuition.
 split.
 assumption.
 split.  
 auto.
 split.
 apply not_gt.
 intro H5.
 rewrite H3_332 in H5.
 omega.  
 intros x H5.
 destruct H5 as [H5_1 [H5_2 H5_3]].
 rewrite H3_332 in H5_3.
 omega.
Qed.

Definition update_pile (p: X.cand -> list (list ballot)) (t: list (X.cand -> Q)) l (q:Q) (c:X.cand): list (list ballot):=   
 if X.cand_in_dec c l 
    then  
        map (map (fun (b : ballot) => 
        (fst b, (Qred (snd b * (Qred ((hd nty t)(c)- q)/(hd nty t)(c))))%Q))) (p c)
    else ( p c).

Definition Update_transVal (c: X.cand) (p: X.cand -> list (list ballot)) (t: X.cand -> Q) :=
 let Sum_parcel := sum (last (p c) []) in
  let r :=  (Qred ((Qred ((t c) - X.quota)) / Sum_parcel)) in
    match (Qlt_le_dec 0 Sum_parcel) with
       left _ => match (Qlt_le_dec r 1) with
                    left _ => r
                   |right _ => (1)%Q
                 end
       |right _ => (1)%Q
    end.


Definition update_pile_ManualACT (p: X.cand -> list (list ballot)) (t: X.cand -> Q) (l: list X.cand) (q:Q) (c: X.cand):=
 if X.cand_in_dec c l
    then
       map (map (fun (b : ballot) =>
         (fst b, (Qred (snd b * (Update_transVal c p t)))%Q))) [(last (p c) [])] 
    else (p c).

(*removes every element of the list k which exist in the list l*)
Fixpoint Removel (k :list X.cand) (l :list X.cand) :list X.cand:=
 match l with
        [] => []
        |l0::ls => if (X.cand_in_dec l0 k) then (Removel k ls) else (l0::(Removel k ls))
 end.

(*if a is not in l, then it is already removed from l*)
Lemma Removel_extra_element: forall a, forall k1 k2 l:list X.cand, ~ In a l -> Removel (k1++[a]++k2) l = Removel (k1++k2) l. 
Proof.
 intros a k1 k2 l H1.
 induction l.
 simpl.
 auto.
 simpl.
 destruct (X.cand_in_dec a0 (k1++k2)) as [ i | j].
 assert (Hyp: ~ In a l).
 intro.
 apply H1.
 right;assumption.
 specialize (IHl Hyp).
 rewrite <- IHl.
 simpl.
 assert (In a0 (k1++[a]++k2)).
 specialize (in_app_or k1 k2 a0 i);intro Hyp2.
 destruct Hyp2 as [Hyp21 |Hyp22].
 intuition.
 intuition.
 destruct (X.cand_in_dec a0 (k1++a::k2)).
 auto.
 contradiction n.
 destruct (X.cand_in_dec a0 (k1++a::k2)).
 assert (Hyp3: ~ In a0 (k1++a::k2)).
 intro.
 specialize (in_app_or k1 (a::k2) a0 H);intro H3.
 destruct H3 as [H4 |H5].
 apply j.
 intuition.
 destruct H5 as [H51 |H52].
 apply H1.
 left.
 symmetry;assumption.
 apply j.
 intuition.
 contradiction Hyp3.
 assert (Hyp4: ~ In a l).
 intro.
 apply H1.
 intuition.
 specialize (IHl Hyp4).
 simpl in IHl.
 rewrite IHl.
 auto.
Qed.

(*to remove particular elements from a list, one can split this removal into two parts*)
Lemma Removel_segmentation: forall k l1 l2: list X.cand, Removel k (l1++l2) = (Removel k l1) ++ (Removel k l2).
Proof.
 intros k l1 l2.
 induction l1.
 simpl.
 auto.
 rewrite<- (app_comm_cons l1 l2 a).
 simpl.
 destruct (X.cand_in_dec a k) as [ i |j].
 assumption.
 rewrite <- (app_comm_cons ).
 rewrite IHl1.
 auto.
Qed.

(*if the orginal list is duplicate-free, so is any remainder list after removal of some elements*)
Lemma Removel_nodup: forall (k l :list X.cand), NoDup l -> NoDup (Removel k l).
Proof.
 intros k l H1.
 induction k.
 assert (Hyp: Removel [] l = l).
 induction l.
 simpl.
 auto.
 simpl.
 destruct (X.cand_in_dec a []).
 inversion i.
 rewrite IHl.
 auto.
 inversion H1.
 assumption.
 rewrite Hyp.
 assumption.
 destruct (X.cand_in_dec a l) as [i | j].
 specialize (in_split a l i);intro H2.
 destruct H2 as [l1 [l2 H3]].
 rewrite H3.
 rewrite (Removel_segmentation (a::k) l1 (a::l2)).
 rewrite H3 in H1.
 specialize (NoDup_remove_2 l1 l2 a H1);intro H4.
 assert (Hyp2: ~ In a l1 /\ ~ In a l2).
 split.
 intuition.
 intuition.
 assert (Hyp3: Removel (a::k) l1 = Removel k l1).
 apply (Removel_extra_element a [] k l1).
 intuition.
 rewrite Hyp3.
 assert (Hyp5: Removel (a::k) (a::l2) = Removel k l2).
 assert (Hypo: a::l2 = [a]++l2).
 simpl.
 auto.
 rewrite Hypo.
 rewrite (Removel_segmentation (a::k) [a] l2).  
 assert (Hyp6: Removel (a::k) [a] = []).
 simpl.
 destruct (X.cand_in_dec a (a::k)).
 auto.
 contradiction n.
 left;auto.
 rewrite Hyp6.
 simpl.
 apply (Removel_extra_element a [] k l2).
 intuition.
 rewrite Hyp5. 
 rewrite H3 in IHk.
 rewrite (Removel_segmentation k l1 (a::l2)) in IHk.
 assert (Hypo: a::l2 = [a]++l2).
 simpl;auto.
 rewrite Hypo in IHk.
 rewrite (Removel_segmentation k [a] l2) in IHk.
 assert (Hypo7: Removel k [a] = [] \/ Removel k [a] = [a]).
 simpl.
 destruct (X.cand_in_dec a k) as [ p | q].
 left;auto.
 right;auto.
 destruct Hypo7 as [Hypo71 | Hypo72].
 rewrite Hypo71 in IHk.
 simpl in IHk.
 assumption.
 rewrite Hypo72 in IHk.
 apply (NoDup_remove_1 (Removel k l1) (Removel k l2) a).
 assumption.
 assert (Hyp: a::k = [a]++k).
 simpl;auto.
 rewrite Hyp.
 assert (Hyp8: [a]++k = []++[a]++k).
 simpl.
 auto.
 rewrite Hyp8.
 rewrite (Removel_extra_element a [] k l).
 simpl.
 assumption.
 assumption.
Qed.

(*if l is a permutation of a list l', then if one changes the position of one element, still he gets a permutation of l*) 
Lemma Permutation_reorder: forall (A :Type) (l: list A) k1 k2, forall a:A, Permutation l (k1++[a]++k2) -> Permutation l ((a::k1)++k2).
Proof.
 intros A l k1 k2 a H1.
 induction k1.
 auto.
 apply (Permutation_trans H1 ).
 apply Permutation_sym.
 rewrite <-(app_comm_cons (a0::k1) k2 a).
 apply Permutation_middle.
Qed.

Lemma Removel_empty: forall k, Removel [] k = k.
Proof.
 intros k.
 induction k.
 simpl.
 auto.
 simpl.
 destruct (X.cand_in_dec a []) as [ i | j].
 inversion i.
 rewrite IHk.
 auto.
Qed.

Lemma nodup_permutation: forall (k l :list X.cand), (forall x, In x k -> In x l) -> NoDup k -> NoDup l -> Leqe (Removel k l) k l.
Proof.
 intros k l H1 H2 H3.
 induction k.
 rewrite (Removel_empty l).
 unfold Leqe.
 simpl.
 apply (Permutation_refl l).
 assert (H12: forall x, In x k -> In x l).
 intros x H.
 apply H1.
 right;auto.
 destruct (X.cand_in_dec a l) as [ i | j].
 specialize (in_split a l i);intro H4.
 destruct H4 as [l1 [l2 H5]].
 assert (Hyp1: Removel (a::k) l = (Removel k l1) ++ Removel k l2).
 rewrite H5.
 rewrite (Removel_segmentation (a::k) l1 (a::l2)).
 rewrite H5 in H3.
 specialize (NoDup_remove_2 l1 l2 a H3);intro H7.
 assert (Hyp2: Removel (a::k) l1 = Removel k l1 /\ Removel (a::k) l2 = Removel k l2).
 split.
 assert (Hyp3: a::k = []++[a]++k).
 simpl;auto.
 rewrite Hyp3.
 apply (Removel_extra_element a [] k l1).
 intuition.
 apply (Removel_extra_element a [] k l2).
 intuition.
 destruct Hyp2 as [Hyp21 Hyp22].
 rewrite Hyp21.
 assert (Hyp3: Removel (a::k) (a::l2) = Removel k l2).
 simpl.
 destruct (X.cand_in_dec a (a::k)) as [p |q].
 apply (Removel_extra_element a [] k l2).
 intuition.
 contradiction q.
 left;auto.
 rewrite Hyp3.
 auto.
 rewrite Hyp1.
 inversion H2.
 specialize (IHk H12 H6).
 rewrite H5 in IHk.
 rewrite (Removel_segmentation k l1 (a::l2))in IHk. 
 assert (Hyp9: a::l2 = [a]++l2).
 simpl;auto.
 rewrite Hyp9 in IHk.
 rewrite (Removel_segmentation k [a] l2) in IHk.
 assert (Hyp10: Removel k [a] = [a]).
 simpl.
 destruct (X.cand_in_dec a k) as [p | q]. 
 contradiction H4.
 auto.
 rewrite Hyp10 in IHk.
 unfold Leqe.
 unfold Leqe in IHk.
 assert (Hyp7: k++(Removel k l1)++[a]++(Removel k l2) = (k++(Removel k l1))++[a]++(Removel k l2)).
 rewrite (app_assoc k (Removel k l1) ([a]++(Removel k l2))).
 auto.
 rewrite Hyp7 in IHk.
 specialize (Permutation_reorder X.cand (l1++[a]++l2) (k++Removel k l1) (Removel k l2) a IHk);intro H7.
 rewrite H5.
 simpl.
 assert (Hyp11: (a::k ++ Removel k l1)++Removel k l2 = a::k++(Removel k l1)++Removel k l2).
 simpl.
 rewrite (app_assoc k (Removel k l1) (Removel k l2)).
 auto.
 rewrite Hyp11 in H7. 
 assumption.
 assert (H: In a (a::k)).
 left;auto.
 specialize (H1 a H).
 contradiction H1.
Qed.

Lemma Permutation_App: forall l l1 l2:list X.cand, Permutation l (l1++l2) -> Permutation l (l2++l1).
Proof.
 intros l l1 l2 H1.
 induction l1.
 rewrite app_nil_r.
 rewrite app_nil_l in H1.
 auto.
 apply (Permutation_trans H1).
 apply (Permutation_app_comm).
Qed.  

Check proj1_sig. 
Lemma Filter_segmentation: forall l a, Filter (a::l) = Filter l \/ (Filter (a::l) = a::Filter l).
Proof.
 intros l a.
 simpl.
 destruct (X.ValidBallot (` (fst a))).
 right.
 reflexivity.
 left.
 auto.
Qed.


Lemma Permutation_reorder2: forall (A:Type) l k1 k2 (a:A), Permutation l ((a::k1)++k2) -> Permutation l (k1++a::k2).
Proof.
 intros A l k1 k2 a.
 intro H.
 induction k1.
 auto.
 apply (Permutation_trans H).
 assert (Hypo: (a::a0::k1)++k2 = a::((a0::k1)++k2)).
 simpl. auto.
 rewrite Hypo.
 apply Permutation_middle.
Qed.

Lemma Filter_Permutation_ballot: forall l:list ballot, exists (l1: list ballot), Permutation (l1++ (Filter l)) l.
Proof.
 intro l.
 induction l.
 simpl.
 exists ([]:list ballot).
 simpl.
 apply Permutation_refl.
 specialize (Filter_segmentation l a);intro H.
 destruct H as [H1| H2].
 rewrite H1.
 destruct IHl as [l1 IHl1].
 exists (a::l1).
 rewrite <- (app_comm_cons).
 apply (perm_skip). assumption.
 rewrite H2.
 destruct IHl as [l1 IHl1].
 exists l1.
 apply Permutation_sym.
 simpl.
 apply (Permutation_reorder2 ballot (a::l) l1 (Filter l) a).
 simpl.
 apply perm_skip.
 apply Permutation_sym.
 assumption.
Qed.

(*End Base_Proofs.*)

(*End Generic_Machine.*)
(*
Section ANUnion.

(* above this line may be added to the base of the framework *)
(* ********************************************************************************************** *)
(* The following excluded lemmas may be proved later *********************************

Lemma List_IsFirst_decompose : forall c h ba acc, (List_IsFirst_Hopeful c h acc ba) = acc \/ 
  (exists l, List_IsFirst_Hopeful c h acc ba = l ++ acc). 

Lemma In_acc_IsIn_List_IsFirst : forall c h acc ba d, In d acc -> In d (List_IsFirst_Hopeful c h acc ba).

Lemma list_is_first_hopeful_Eq_List_IsFirst_Hopeful : 
 forall c h ba, forall b, In b (list_is_first_hopeful c h ba) -> In b (List_IsFirst_Hopeful c h [] ba).
*) 


Definition Union_InitStep (prem :Machine_States) (conc :Machine_States): Prop :=
 exists ba ba',  
  prem = initial ba /\
  ba' = (Filter ba) /\
  conc = state(ba', [nty], nas, (nbdy, nbdy), emp_elec, all_hopeful).

Lemma UnionInitStep_SanityCheck_App : SanityCheck_Initial_App Union_InitStep.
Proof.
 unfold SanityCheck_Initial_App.  
 intros.
 exists (state (Filter ba, [nty], nas, (nbdy, nbdy), emp_elec, all_hopeful)). 
 split. auto.
 unfold Union_InitStep.
 exists ba.
 exists (Filter ba).
 split. assumption.
 split;auto. 
Qed. 

Lemma UnionInitStep_SanityCheck_Red: SanityCheck_Initial_Red Union_InitStep.
 unfold SanityCheck_Initial_Red.
 intros.
 unfold Union_InitStep in H.
 destruct H as [ba [ba' H1]]. 
 exists ba. exists ba'. exists [nty]. exists nas. exists (nbdy, nbdy). exists emp_elec. exists all_hopeful.
 split;auto.
 intuition.
 intuition.
Qed.

Definition Union_count (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists ba t nt p np bl h e,                (** count the ballots requiring attention **)
  prem = state (ba, t, p, bl, e, h) /\     (* if we are in an intermediate state of the count *) 
  [] <> ba /\                                        (* and there are ballots requiring attention *)
  (forall c, if (cand_in_dec c (proj1_sig h)) 
      then 
  (exists l,                     
    np(c) = p(c) ++ [l] /\                       
    (forall b, In (proj1_sig (fst b)) (map (fun (d:ballot) => (proj1_sig (fst d))) l) <-> 
                                                               fcc ba (proj1_sig h) c b) /\ 
    (nt (c) = SUM (np(c)))) 
      else ((nt c) = (hd nty t) c) /\ (np c) = (p c)) /\                 
  conc = state ([], nt :: t, np, bl, e, h).     

Hypothesis Bl_hopeful_NoIntersect : forall j: Machine_States, forall ba t p bl e h, j = state (ba,t,p,bl,e,h) ->
 (forall c, In c (snd bl) -> ~ In c (proj1_sig h)) * (forall c, In c (fst bl) -> ~ In c (snd bl)).

Lemma UnionCount_SanityCheck_App : SanityCheck_Count_App Union_count.
Proof.
 unfold SanityCheck_Count_App. 
 intros.
 exists (state ([], (fun (c:cand) =>  if (cand_in_dec c (proj1_sig h)) then SUM (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (hd nty t) c) :: t, fun (c:cand) => (if (cand_in_dec c (proj1_sig h)) then (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (p c)), bl, e, h)).
 unfold Union_count.
 exists ba.
 exists t.
 exists ((fun (c:cand) =>  if (cand_in_dec c  (proj1_sig h)) then SUM (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else ((hd nty t) c))).
 exists p.
 exists (fun (c:cand) => (if (cand_in_dec c (proj1_sig h)) then (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (p c))). 
 exists bl.
 exists h.
 exists e.
 split; auto.
 split; auto.
 split.
 intro c.
 destruct (cand_in_dec c (proj1_sig h)).
 exists (list_is_first_hopeful c (proj1_sig h) ba).
 split; auto.
 split.
 intro b.   
 apply (listballot_fcc ba t p bl e h quota c i b). 
 simpl.
 destruct (cand_in_dec c (proj1_sig h)). auto.
 contradict n. assumption.
 simpl.
 destruct (cand_in_dec c (proj1_sig h)).
 contradict n. assumption.
 auto. auto.
Qed.

Lemma UnionCount_SanityCheck_Red: SanityCheck_Count_Red Union_count.
 Proof.
 unfold SanityCheck_Count_Red.
 intros.
 unfold Union_count in H.
 destruct H as [ba [t [nt [ p0 [np [bl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 assert (old_new_pile_equal_bl: forall c, In c (snd bl) -> p0 c = np c).
 specialize (Bl_hopeful_NoIntersect p ba t p0 bl e h H11). 
 intros c0  Hyp.
 destruct Bl_hopeful_NoIntersect as [NoIntersect1 NoIntersect2].
 specialize (NoIntersect1 c0 Hyp).
 specialize (H13 c0).
 destruct (cand_in_dec c0 (proj1_sig h)).
 contradict NoIntersect1.
 assumption.
 intuition.
 exists ba; exists ([]: list ballot); exists t. exists nt; exists p0. 
 exists np; exists bl; exists e; exists h. split. intuition. 
 split; intuition.
 specialize (list_nonempty ballot ba). intro Hyp.
 intuition.
 destruct H as [b [l Hyp1]].
 rewrite Hyp1.
 simpl. 
 omega. 
 assert (hyp2: forall c, In c (snd bl) -> length (concat (p0 c)) = length (concat (np c))).
 intros.
 specialize (old_new_pile_equal_bl c0 H). 
 rewrite old_new_pile_equal_bl.
 reflexivity.
 specialize (map_ext_in (fun c0 => length (concat (p0 c0))) (fun c0 => length (concat (np c0))) (snd bl) hyp2).
 intro.
 rewrite H. auto.
Qed.

Definition Union_hwin (prem: Machine_States) (conc: Machine_States) : Prop :=
  exists w ba t p bl e h,                            
   prem = state (ba, t, p, bl, e, h) /\           
   length (proj1_sig e) + length (proj1_sig h) <= st /\ 
   w = (proj1_sig e) ++ (proj1_sig h) /\                        
   conc = winners (w).

Lemma  UnionHwin_SanityCheck_App : SanityCheck_Hwin_App Union_hwin.                           
Proof.
 unfold SanityCheck_Hwin_App.
 intros.
 unfold Union_hwin.
 exists (winners ((proj1_sig e) ++ (proj1_sig h))).
 exists ((proj1_sig e) ++ (proj1_sig h)).
 exists ba; exists t; exists p; exists bl; exists e; exists h.  
 auto.
Qed.

Lemma UnionHwin_SanityCheck_Red : SanityCheck_Hwin_Red Union_hwin.
Proof.
 unfold SanityCheck_Hwin_Red.
 intros.
 unfold Union_hwin in H. 
 destruct H as [w [ba [t [p [bl [e [h H1]]]]]]]. 
 exists w; exists ba; exists t; exists p; exists bl; exists e; exists h. 
 intuition.
Qed.

Definition Union_ewin (prem: Machine_States) (conc: Machine_States) : Prop :=
  exists w ba t p bl e h,                    (** elected win **)
   prem = state (ba, t, p, bl, e, h) /\   (* if at any time *)
   length (proj1_sig e) = st /\             (* we have as many elected candidates as seats *) 
   w = (proj1_sig e) /\                        (* and the winners are precisely the electeds *)
   conc = winners (w).                      (* they are declared the winners *)

Lemma UnionEwin_SanityCheck_App : SanityCheck_Ewin_App Union_ewin.
Proof.
 unfold SanityCheck_Ewin_App.
 intros.
 unfold Union_ewin.
 exists (winners (proj1_sig e)). 
 exists (proj1_sig e). exists ba. exists t. exists p. exists bl. exists e. exists h.
 intuition.
Qed.

Lemma UnionEwin_SanityCheck_Red : SanityCheck_Ewin_Red Union_ewin.
Proof.
 unfold SanityCheck_Ewin_Red.
 intros.
 unfold Union_ewin in H.
 destruct H as [w [ba [t [p [bl [e [h H1]]]]]]].
 exists w. exists ba. exists t. exists p. exists bl. exists e. exists h. 
 intuition.
 rewrite <- H0.
 assumption.
Qed.

Definition Union_transfer (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists nba t p np bl nbl h e,         (** transfer votes **) 
  prem = state ([], t, p, bl, e, h) /\ 
    (length (proj1_sig e) < st) /\
    (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\        (* and we can't elect any candidate *)
    exists l c,                          (* and there exists a list l and a candidate c *)
     (bl = (c :: l, []) /\                     (* such that c is the head of the backlog *)
     nbl = (l, []) /\                          (* and the backlog is updated by removing the head c *)
     nba = flat_map (fun x => x) (p c) /\            (* and the pile of ballots for c is the new list of ballots requiring attention *)
     np(c) = [] /\                                (* and the new pile for c is empty *)
     (forall d, d <> c -> np(d) = p(d))) /\ (* and the piles for every other candidate remain the same *)   
   conc = state (nba, t, np, nbl, e, h).  

Lemma UnionTransfer_SanityCheck_App : SanityCheck_Transfer1_App Union_transfer.
Proof.
 unfold SanityCheck_Transfer1_App.
 intros.
 unfold Union_transfer.
 destruct H0 as [H01 [H02 H03]]. 
 specialize (list_nonempty_type cand (fst bl) H02). intro Nonempty_bl.
 destruct Nonempty_bl as [c s].  
 destruct s as [bls H3].  
 exists (state (flat_map (fun x => x) (p c), t, fun d => 
                                                        if (cand_eq_dec d c) then [] else p d, 
                                                        (bls, []), e, h)).
 exists (flat_map (fun x => x) (p c)). exists t. exists p. 
 exists (fun d => if (cand_eq_dec d c) then [] else p d). exists (c::bls, ([]: list cand)). 
 exists (bls, ([]: list cand)). exists h.
 exists e. 
 intuition.
 rewrite H3 in H. assumption.
 exists bls. exists c.
 intuition.
 destruct (cand_eq_dec c c). reflexivity.
 contradict f. auto.
 destruct (cand_eq_dec d c).
 contradict H0. assumption.
 auto.
Qed.

Lemma UnionTransfer_SanityCheck_Red : SanityCheck_Transfer_Red Union_transfer.
 Proof.
 unfold SanityCheck_Transfer_Red.
 intros.
 unfold Union_transfer in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [l [ c H141]].
 exists nba; exists t; exists p; exists np; exists bl; exists nbl; exists h; exists e.
 intuition.
 left.
 rewrite H1.
 rewrite H.
 simpl.
 omega.
Qed.

Definition Union_elim (prem: Machine_States) (conc: Machine_States) : Prop :=
  exists nba t p np e h nh bl2,                    
   prem = state ([], t, p, ([], bl2), e, h) /\         
   length (proj1_sig e) + length (proj1_sig h) > st /\ 
   (forall c, In c (proj1_sig h) -> (hd nty t(c) < quota)%Q) /\ 
   exists c,                                            
     ((forall d, In d (proj1_sig h) -> (hd nty t(c) <= hd nty t(d)))%Q /\            
     eqe c (proj1_sig nh) (proj1_sig h) /\                                   
     nba = flat_map (fun x => x) (p c) /\                                   
     np(c)=[] /\                                       
     (forall d, d <> c -> np (d) = p (d)) /\                       
   conc = state (nba, t, np, ([], []), e, nh)). 

Lemma UnionElim_SanityCheck_App : SanityCheck_Elim_App Union_elim.
Proof.
 unfold SanityCheck_Elim_App.
 intros.
 unfold Union_elim.
 specialize (list_min cand (proj1_sig h) (hd nty t)). intro min_hopeful.
 destruct min_hopeful.
 rewrite e0 in H0.
 destruct H0 as [H01 H02].
 destruct e.
 simpl in H01.
 omega.
 destruct s as [min [s1 s2]].
 specialize (remc_nodup (proj1_sig h) min (proj2_sig h) s1);intro H'1.
 exists (state (flat_map (fun x => x) (p min), t, fun d => if (cand_eq_dec d min) then [] else (p d),
                                                ([], []), e, exist _ (remc min (proj1_sig h)) H'1)). 
 exists (flat_map (fun x => x) (p min)).
 exists t. exists p. exists (fun d => if (cand_eq_dec d min) then [] else (p d)). exists e. exists h. 
 exists (exist _ (remc min (proj1_sig h)) H'1).
 intuition.
 exists bl2.
 intuition.
 simpl.
 exists min.
 intuition.
 apply (remc_ok min (proj1_sig h) (proj2_sig h) s1).
 destruct (cand_eq_dec min min). reflexivity.
 contradict f. auto.
 destruct (cand_eq_dec d min). contradiction H0. reflexivity.
Qed.

Lemma UnionElim_SanityCheck_Red : SanityCheck_Elim_Red Union_elim.
 Proof.
 unfold SanityCheck_Elim_Red.
 intros. 
 unfold Union_elim in H.
 destruct H as [nba [t [p [np [e [h [nh [bl2 H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [weakest H141]. 
 exists nba. exists t. exists p. exists np. exists e. exists h. exists nh.  
 intuition.
 unfold eqe in H1.
 destruct H1 as [l1 [l2 [H' [H'' [H''' H'''']]]]].
 rewrite H'.
 rewrite H''.
 assert (Hyp : length (l1 ++ [weakest] ++ l2) = (length l1 + (length ([weakest] ++ l2)))% nat).
 simpl.
 rewrite (app_length).
 simpl. auto.  
 rewrite Hyp.
 simpl.
 rewrite (app_length).
 exists bl2. 
 exists ([]: list cand).
 intuition.
Qed.

Definition Union_elect (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists t p np (bl nbl: (list cand) * (list cand)) (nh h: {hopeful: list cand | NoDup hopeful})(e ne: {l : list cand | length l <= st }),
    prem = state ([], t, p, bl, e, h) /\ 
    exists l,                                      
     (l <> [] /\                                  
     length l <= st - length (proj1_sig e) /\    
     (forall c, In c l -> In c (proj1_sig h) /\ (hd nty t (c) >= quota)%Q) /\      
     ordered (hd nty t) l /\ 
     Leqe l (proj1_sig nh) (proj1_sig h) /\          
     Leqe l (proj1_sig e) (proj1_sig ne) /\     
     (forall c, In c l -> ((np c) = map (map (fun (b : ballot) => 
        (fst b, (Qred (snd b * (Qred ((hd nty t)(c)- quota)/(hd nty t)(c))))%Q))) (p c))) /\  
     (forall c, ~ In c l -> np (c) = p (c)) /\  
    fst nbl = (fst bl) ++ l) /\                                 
  conc = state ([], t, np, nbl, ne, nh).      

Lemma UnionElect_SanityCheck_App : SanityCheck_Elect_App Union_elect.
Proof.
 unfold SanityCheck_Elect_App.
 intros.
 unfold Union_elect.
 specialize (constructing_electable_first).  
 intro H1.
 destruct X as [c [X1 X2]].
 assert (Hyp: length (proj1_sig e) < st).
 omega.
 specialize (H1 e (hd nty t) h quota Hyp (proj2_sig h)).
 destruct H1 as [listElected H11].
 destruct H11 as [H111 [H112 [H113 [H114 H115]]]].
 specialize (Removel_nodup listElected (proj1_sig h) (proj2_sig h)). intro NoDupH.
 assert (Assum: length ((proj1_sig e) ++ listElected) <= st).
 rewrite app_length.
 omega.
 exists (state ([], t, fun c => update_pile p t listElected quota c, ((fst bl) ++ listElected, snd bl), 
 exist _ ((proj1_sig e) ++ listElected) Assum, exist _ (Removel listElected (proj1_sig h)) NoDupH)).
 exists t. exists p. exists (fun x => update_pile p t listElected quota x).
 exists bl. exists ((fst bl) ++ listElected, snd bl). exists (exist _ (Removel listElected (proj1_sig h)) NoDupH).
 exists h. exists e. exists (exist (fun v => length v <= st) ((proj1_sig e) ++ listElected) Assum). 
 split. auto.
 exists listElected.
 intuition.
 assert (NonEmptyElected: length listElected = 0). 
 rewrite H2.
 simpl. reflexivity.
 assert (VacantSeat: length (listElected) < st - (length (proj1_sig e))).
 rewrite app_length in Assum.
 rewrite NonEmptyElected in Assum.
 omega.
 specialize (H115 c). 
 intuition.
 rewrite H2 in H3.
 inversion H3.
 simpl.
 unfold Leqe.
 apply Permutation_App.
 apply (nodup_permutation).
 intros candid HypCand. 
 specialize (H111 candid HypCand).
 intuition.
 assumption. 
 apply (proj2_sig h).
 simpl.
 unfold Leqe.
 apply Permutation_refl.
 unfold update_pile.
 destruct (cand_in_dec c0 listElected).
 trivial.
 contradict f. assumption.
 unfold update_pile.
 destruct (cand_in_dec c0 listElected).
 contradict H2.
 assumption.
 auto.
Qed.

Lemma UnionElect_SanityCheck_Red : SanityCheck_Elect_Red Union_elect.
Proof.
 unfold SanityCheck_Elect_Red.
 intros.
 unfold Union_elect in H.
 destruct H as [t [p [np [bl [nbl [nh [h [e [ne H1]]]]]]]]].
 exists t. exists p; exists np. exists bl. exists nbl. exists e. exists ne. exists nh. exists h. 
 destruct H1 as [H11 H12].
 destruct H12 as [l H121].
 intuition.
 unfold Leqe in H4.  
 specialize (Permutation_length H4). intro Permut_length.
 rewrite Permut_length.
 rewrite  app_length.
 specialize (list_nonempty_type cand l H1). intro.
 destruct X as [c [l' HX]].
 rewrite HX.
 simpl. 
 omega.
 unfold Leqe in H5.
 specialize (Permutation_length H5). intro.
 rewrite H8.
 rewrite app_length.
 specialize (list_nonempty_type cand l H1). intro.
 destruct X as [c [l' HX]]. 
 rewrite HX.
 simpl.
 omega.
Qed.

Definition Union_quota := 
 (((inject_Z (Z.of_nat (length (Filter bs)))) / (1 + inject_Z (Z.of_nat st)) + 1)%Q). 

Definition VicTas_TransferElected2 (prem: Machine_States) (conc: Machine_States) :=
 exists nba t p np bl nbl h e,         
  prem = state ([], t, p, bl, e, h) /\ 
    (length (proj1_sig e) < st) /\
    (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\       
    exists l c c' l',                          
     (bl = (c :: l, c'::l') /\                   
     nbl = (l, l') /\                          
     nba = concat (p c) /\
     concat (p c') = [] /\           
     np(c) = [] /\                                 
     (forall d, d <> c -> np(d) = p(d))) /\    
   conc = state (nba, t, np, nbl, e, h). 

Lemma VicTasTran2_SanityCheck_App : SanityCheck_Transfer2_App VicTas_TransferElected2. 
Proof.
 unfold SanityCheck_Transfer2_App.
 intros. 
 unfold VicTas_TransferElected2.
 destruct H0 as [H1 [H2 [H3 H4]]].
 specialize (list_nonempty_type cand bl1 H2). intro Nonempty_bl.
 destruct Nonempty_bl as [Headbl1 [Tailbl1 bl1None]].
 
 exists (state (concat (p Headbl1), t, fun x => if (cand_eq_dec x Headbl1) then [] else p x, 
                (Tailbl1, bl2), e, h)).  
 exists (concat (p Headbl1)).
 exists t. exists p. exists (fun x => if (cand_eq_dec x Headbl1) then [] else (p x)).
 exists (Headbl1:: Tailbl1, c:: bl2). exists (Tailbl1,bl2). exists h. exists e.
 rewrite bl1None in H.
 intuition.
 exists Tailbl1. exists Headbl1. exists c. exists bl2.
 intuition.
 destruct (cand_eq_dec Headbl1 Headbl1).
 reflexivity.
 contradict f.  auto.
 destruct (cand_eq_dec d Headbl1).
 contradict H0.
 auto.
 reflexivity.
Qed.

Lemma VicTasTran2_SanityCheck_Red : SanityCheck_Transfer_Red VicTas_TransferElected2.
Proof.
 unfold SanityCheck_Transfer_Red.
 intros.
 unfold VicTas_TransferElected2 in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [Tbl1 [Hbl1 [Hbl2 [Tbl2 H15]]]].
 exists nba.
 exists t. exists p. exists np. exists bl. exists nbl. exists h. exists e.
 destruct H15 as [H15 H152].
 destruct H15 as [HH1 HH2].
 destruct HH2 as [HH21 [HH22 [HH23 [HH24 HH25]]]].
 assert (Hypo: forall d, In d Tbl2 -> p (d) = np (d)).
 intros d Hy.
 assert (hypos: d <> Hbl1). intro contHypos. rewrite contHypos in Hy.
 specialize (Bl_hopeful_NoIntersect (state ([],t,p,bl, e,h)) [] t p bl e h (eq_refl)).  
 destruct Bl_hopeful_NoIntersect as [i j]. 
 specialize (j Hbl1).
 rewrite HH1 in j.
 assert (hyu: In Hbl1 (fst (Hbl1:: Tbl1, Hbl2:: Tbl2))).
 simpl. left;auto.
 specialize (j hyu).
 apply j.
 simpl.
 right;assumption.
 specialize (HH25 d hypos).
 auto.
 split.  auto.
 split. left. rewrite HH1. rewrite HH21. 
 simpl. rewrite HH23.
 assert (Leneq: forall d, In d Tbl2 -> length (concat (p d)) = length (concat (np d))).
 intros d he.
 specialize (Hypo d he). rewrite Hypo. auto.
 specialize (map_ext_in (fun c => length (concat (p c))) (fun d => length (concat (np d))) Tbl2 Leneq). 
 intro map_equal.
 rewrite map_equal.
 simpl.
 omega.
 auto.
Qed.

Definition VicTas_TransferElim (prem: Machine_States) (conc: Machine_States) :=
 exists nba t p np bl nbl h e,         
  prem = state ([], t, p, bl, e, h) /\ 
    (length (proj1_sig e) < st) /\
    (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\       
    exists l c c' l',                          
     (bl = (c :: l, c'::l') /\                   
     nbl = (c::l, c'::l') /\
      (concat (p c') <> []) /\ 
      let x:= (groupbysimple _ (sort (concat (p c')))) in
       (nba = last x []) /\
       np c' = (removelast x) /\                                        
     (forall d, d <> c' -> np(d) = p(d))) /\    
   conc = state (nba, t, np, nbl, e, h). 

Hypothesis Bl_NoDup : forall j: Machine_States, forall ba t p bl e h, 
  j = state (ba,t,p,bl,e,h) -> NoDup (snd bl).


Lemma VicTas_TransferElim_SanityCheck_App : SanityCheck_Transfer3_App VicTas_TransferElim.
Proof.
 unfold SanityCheck_Transfer3_App.
 intros.
 destruct H0 as [H1 [H2 [H3 H4]]].
 unfold VicTas_TransferElim.
 exists (state (((last (groupbysimple _ (sort (concat (p c)))) []): list ballot),
 t, fun d => if (cand_eq_dec d c) then (removelast (groupbysimple _ (sort (concat (p c))))) else p d, (bl1, c::bl2), e, h)). 
 exists (last (groupbysimple _ (sort (concat (p c)))) []). 
 exists t. exists p. exists (fun d => if (cand_eq_dec d c) 
   then (removelast ((groupbysimple _ (sort (concat (p c))))))  else p d). 
 exists (bl1,c::bl2). exists (bl1, c::bl2). exists h. exists e. intuition.
 specialize (list_nonempty_type cand bl1 H2). intro Nbl1.
 destruct Nbl1 as [Hbl1 [Tbl1 bl1N]].
 exists Tbl1. exists Hbl1. exists c. exists bl2.
 rewrite bl1N.
 intuition.
 destruct (cand_eq_dec c c) as [i | j].
 auto. contradict j. reflexivity.
 destruct (cand_eq_dec d c) as [i |j].
 contradiction H0. reflexivity.
Qed.

Lemma concat_app : forall (A:Type) (l1: list (list A)) l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
Proof.
  intros.
  induction l1 as [|x l1 IH]. induction l2. simpl.
  reflexivity. simpl. auto.
  simpl. rewrite IH; apply app_assoc.
Qed.
 
Lemma VicTas_TransferElim_SanityCheck_Red: SanityCheck_Transfer_Red VicTas_TransferElim.
Proof.
 unfold SanityCheck_Transfer_Red. 
 intros.
 unfold VicTas_TransferElim in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [Tbl1 [Hbl1 [Hbl2 [Tbl2 H15]]]].
 destruct H15 as [H151 H152].  
 destruct H151 as [K1 K2].
 destruct K2 as [K21 [K22 [K23 [K24 K25]]]].
 exists nba. exists t. exists p. exists np. exists bl. exists nbl. exists h. exists e.
 split. assumption.
 split. right. rewrite K1. rewrite K21. simpl. split. auto.
 assert (Tbl2_NoDup: NoDup (Hbl2 :: Tbl2)). 
 specialize (Bl_NoDup (state ([],t,p,bl,e,h)) [] t p bl e h (eq_refl)).
 rewrite K1 in Bl_NoDup.
 simpl in Bl_NoDup.
 assumption.
 assert (Hbl2_notInTail: ~ In Hbl2 Tbl2). 
 intro Cont.
 inversion Tbl2_NoDup.
 apply H1. assumption.
 assert (Piles_eq_Tbl2: forall d, In d Tbl2 -> p d = np d).
 intros d InTbl2.
 assert (not_eq_d: d <> Hbl2).
 intro cont. rewrite cont in InTbl2. apply Hbl2_notInTail. assumption.
 specialize (K25 d not_eq_d).
 auto.
 assert (Len_piles_eq: forall d, In d Tbl2 -> length (concat (p d)) = length (concat (np d))).
 intros d Hy.
 specialize (Piles_eq_Tbl2 d Hy).
 rewrite Piles_eq_Tbl2. auto.
 specialize (map_ext_in (fun c => length (concat (p c))) (fun c => length (concat (np c))) Tbl2 Len_piles_eq). 
 intro nice.
 rewrite nice.  
 rewrite K24.
 assert (Hypo: (groupbysimple _ (sort (concat (p Hbl2)))) <> []).
 apply groupbysimple_not_empty.
 apply sherin. 
 auto.  
 assert (Hypo2: groupbysimple _ (sort (concat (p Hbl2))) = 
(removelast (groupbysimple _ (sort (concat (p Hbl2))))) ++ [last (groupbysimple _ (sort (concat (p Hbl2)))) []]).
 apply app_removelast_last.
 assumption.
 assert (Hypo222: concat (groupbysimple _ (sort (concat (p Hbl2)))) =
                  concat ((removelast (groupbysimple _ (sort (concat (p Hbl2)))))
                            ++
                            [last (groupbysimple _ (sort (concat (p Hbl2)))) []])).
 apply f_equal. assumption.
 rewrite concat_app in Hypo222. 

 assert (Hypo22: length (concat (groupbysimple _ (sort (concat (p Hbl2))))) = 
 (length (concat (removelast (groupbysimple _ (sort (concat (p Hbl2)))))) + 
  length (concat [last (groupbysimple _ (sort (concat (p Hbl2)))) []]))%nat).
 rewrite <- app_length. apply f_equal. auto.
 assert (Hypolen : length
            (concat (groupbysimple {v : list cand | NoDup v /\ [] <> v} (sort (concat (p Hbl2))))) = 
                   length (concat (p Hbl2))).
 rewrite <- concat_rat. auto.
 rewrite <- Hypolen.
 rewrite  Hypo22.
 simpl.
 assert (Hlen : forall (A : Type) (l : list A),
            l <> []  -> 0 < length l).  
 intros. destruct l. contradiction H. auto. simpl. omega.
 specialize (groupby_notempty _ (sort (concat (p Hbl2)))). intros.
 pose proof (sortedList_notempty (concat (p Hbl2)) K22).
 specialize (H H0). 
 specialize (Hlen _ _ H).
 rewrite app_nil_r.
 apply Nat.add_lt_mono_r.
 apply NPeano.Nat.lt_add_pos_r. trivial.
 auto.
Qed.

Definition UnionSTV := (mkSTV (quota)  
    (Union_InitStep) (UnionInitStep_SanityCheck_App) (UnionInitStep_SanityCheck_Red) 
    (Union_count) (UnionCount_SanityCheck_App) (UnionCount_SanityCheck_Red)
    (Union_transfer) (UnionTransfer_SanityCheck_App) (UnionTransfer_SanityCheck_Red)
    (VicTas_TransferElected2) (VicTasTran2_SanityCheck_App) (VicTasTran2_SanityCheck_Red)
    (VicTas_TransferElim) (VicTas_TransferElim_SanityCheck_App) (VicTas_TransferElim_SanityCheck_Red)
    (Union_elect) (UnionElect_SanityCheck_App) (UnionElect_SanityCheck_Red)
    (Union_elim) (UnionElim_SanityCheck_App) (UnionElim_SanityCheck_Red)
    (Union_hwin) (UnionHwin_SanityCheck_App) (UnionHwin_SanityCheck_Red)
    (Union_ewin) (UnionEwin_SanityCheck_App) (UnionEwin_SanityCheck_Red)).


Lemma init_stages_R_initial : ~ State_final (initial (Filter bs)).
Proof.
 intro.
 unfold State_final in H.
 destruct H.
 inversion H.
Qed.
 
Definition Union_Termination := Termination (initial (Filter bs)) init_stages_R_initial UnionSTV.

End ANUnion.
*)
(*
Definition ACT_TransferElected (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists nba t p np bl nbl h e,
  prem = state ([], t, p, bl, e, h) /\
  (length (proj1_sig e) < st) /\
  (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\
  exists l c,
   (bl = (c :: l,[]) /\
   nbl = (l,[]) /\
   nba = last (p c) [] /\ np(c) = [] /\
     (forall d, d <> c -> np(d) = p(d))) /\
   conc = state (nba, t, np, nbl, e, h).

Lemma ACT_TransferElected_SanityCheck_App : SanityCheck_Transfer1_App ACT_TransferElected.
Proof.
 unfold SanityCheck_Transfer1_App.
 intros.
 destruct H0 as [H1 [H2 H3]].
 specialize (list_nonempty_type cand (fst bl) H2). intro Hyp. destruct Hyp as [head [tail Hyp1]].
 exists (state (last (p head) [], t, fun d => if (cand_eq_dec d head) then [] else (p d), (tail,[]), e, h)).
 unfold ACT_TransferElected. exists (last (p head) []). exists t. exists p.
 exists (fun d => if (cand_eq_dec d head) then [] else (p d)).
 exists (head::tail, []). exists (tail,[]). exists h. exists e. rewrite Hyp1 in H. simpl in H.
 intuition.
 exists tail. exists head.
 intuition.
 destruct (cand_eq_dec head head). reflexivity. contradict f. auto.
 destruct (cand_eq_dec d head). contradiction H0. reflexivity.
Qed.

Lemma ACT_TransferElected_SanityCheck_Red : SanityCheck_Transfer_Red ACT_TransferElected.
Proof.
 unfold SanityCheck_Transfer_Red.
 intros.
 unfold ACT_TransferElected in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [l [candid H141]].
 destruct H141 as [H1411 H1412].
 destruct H1411 as [H3 [H4 H5]].
 exists nba. exists t. exists p. exists np. exists bl. exists nbl. exists h. exists e.
 intuition.  
 rewrite H3.
 rewrite H4.
 simpl.
 left.
 omega.
Qed.


(* transfer value has changed so that only last parcel is to be transferred at a Manual_ACT rate*)
(* note that only the last parcel is kept after being updated. The rest of the parcel is thrown out! *)
Definition ACT_Elect (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists t p np (bl nbl: (list cand) * (list cand)) nh h (e ne: {l : list cand | length l <= st }),
    prem = state ([], t, p, bl, e, h) /\
    exists l,
     (l <> [] /\
     length l <= st - length (proj1_sig e) /\
     (forall c, In c l -> In c (proj1_sig h) /\ (hd nty t (c) >= quota)%Q) /\    
     ordered (hd nty t) l /\
     Leqe l (proj1_sig nh) (proj1_sig h) /\
     Leqe l (proj1_sig e) (proj1_sig ne) /\
     (forall c, In c l -> ((np c) = map (map (fun (b : ballot) =>
         (fst b, (Qred (snd b * (Update_transVal c p (hd nty t))))%Q))) [(last (p c) [])])) /\
     (forall c, ~ In c l -> np (c) = p (c)) /\
     fst nbl = (fst bl) ++ l) /\
  conc = state ([], t, np, nbl, ne, nh).

Lemma ACT_Elect_SanityCheck_App : SanityCheck_Elect_App ACT_Elect.
Proof.
 unfold SanityCheck_Elect_App. 
 intros.
 unfold ACT_Elect.
 specialize (constructing_electable_first).
 intro H1.
 destruct X as [c [X1 X2]].
 assert (Hyp: length (proj1_sig e) < st).
 omega. 
 specialize (H1 e (hd nty t) h quota Hyp (proj2_sig h)).
 destruct H1 as [listElected H11].
 destruct H11 as [H111 [H112 [H113 [H114 H115]]]].
 specialize (Removel_nodup listElected (proj1_sig h) (proj2_sig h)). intro NoDupH.
 assert (Assum: length ((proj1_sig e) ++ listElected) <= st).
 rewrite app_length.
 omega.
 exists (state ([], t, fun c => update_pile_ManualACT p (hd nty t) listElected quota c, 
((fst bl) ++ listElected, snd bl), exist _ ((proj1_sig e) ++ listElected) Assum, 
                                   exist _ (Removel listElected (proj1_sig h)) NoDupH)). 
 exists t. exists p. exists (fun x => update_pile_ManualACT p (hd nty t) listElected quota x).
 exists bl. exists ((fst bl) ++ listElected, snd bl). exists (exist _ (Removel listElected (proj1_sig h)) NoDupH).
 exists h. exists e. exists (exist _ ((proj1_sig e) ++ listElected) Assum).
 split. auto.
 exists listElected.
 intuition.
 assert (NonEmptyElected: length listElected = 0).
 rewrite H2.
 simpl. reflexivity.
 assert (VacantSeat: length (listElected) < st - (length (proj1_sig e))).
 rewrite app_length in Assum.
 rewrite NonEmptyElected in Assum.
 omega.
 specialize (H115 c).
 intuition. 
 rewrite H2 in H3.
 inversion H3. 
 simpl.
 unfold Leqe.
 apply Permutation_App.
 apply (nodup_permutation).
 intros candid HypCand. 
 specialize (H111 candid HypCand).
 intuition. 
 assumption.
 apply (proj2_sig h).
 simpl.
 unfold Leqe.
 apply Permutation_refl.
 unfold update_pile_ManualACT.
 destruct (cand_in_dec c0 listElected).
 trivial. 
 contradict f. assumption.
 unfold update_pile_ManualACT.
 destruct (cand_in_dec c0 listElected).
 contradict H2.
 assumption.
 auto. 
Qed.

Lemma ACT_Elect_SanityCheck_Red : SanityCheck_Elect_Red ACT_Elect.
Proof.
 unfold SanityCheck_Elect_Red.
 intros.
 unfold ACT_Elect in H.
 destruct H as [t [p [np [bl [nbl [nh [h [e [ne H1]]]]]]]]].
 exists t. exists p; exists np. exists bl. exists nbl. exists e. exists ne. exists nh. exists h. 
 destruct H1 as [H11 H12].
 destruct H12 as [l H121].
 intuition.
 unfold Leqe in H4.
 specialize (Permutation_length H4). intro Permut_length.
 rewrite Permut_length.
 rewrite  app_length.
 specialize (list_nonempty_type cand l H1). intro.
 destruct X as [c [l' HX]].
 rewrite HX.
 simpl.  
 omega.  
 unfold Leqe in H5.
 specialize (Permutation_length H5). intro.
 rewrite H8.
 rewrite app_length.
 specialize (list_nonempty_type cand l H1). intro.
 destruct X as [c [l' HX]]. 
 rewrite HX.
 simpl.
 omega.
Qed.


Definition ActSTV := (mkSTV (quota)  
    (Union_InitStep) (UnionInitStep_SanityCheck_App) (UnionInitStep_SanityCheck_Red) 
    (Union_count) (UnionCount_SanityCheck_App) (UnionCount_SanityCheck_Red)
    (ACT_TransferElected) (ACT_TransferElected_SanityCheck_App) (ACT_TransferElected_SanityCheck_Red)
    (VicTas_TransferElected2) (VicTasTran2_SanityCheck_App) (VicTasTran2_SanityCheck_Red)
    (VicTas_TransferElim) (VicTas_TransferElim_SanityCheck_App) (VicTas_TransferElim_SanityCheck_Red)
    (ACT_Elect) (ACT_Elect_SanityCheck_App) (ACT_Elect_SanityCheck_Red)
    (Union_elim) (UnionElim_SanityCheck_App) (UnionElim_SanityCheck_Red)
    (Union_hwin) (UnionHwin_SanityCheck_App) (UnionHwin_SanityCheck_Red)
    (Union_ewin) (UnionEwin_SanityCheck_App) (UnionEwin_SanityCheck_Red)).

Lemma init_stages_R_initial : ~ State_final (initial (Filter bs)).
Proof.
 intro.
 unfold State_final in H.
 destruct H.
 inversion H.
Qed.
 
Definition Act_Termination := Termination (initial (Filter bs)) init_stages_R_initial ActSTV.



 (* Below is the transfer rule changed so that all backlog is emptied in one go *)
 (* Replacing this Transfer with Union_transfer, gets us close to ACT Legislative Assembly *)

(*
Lemma Emptying_Piles_Correct1 : forall (d: cand) (bl :list cand) (p: cand -> list (list ballot)), 
 In d bl -> (fun c => if (cand_in_dec c bl) then [] else p (c)) d = []. 
Proof.
 intros.
 simpl.
 destruct (cand_in_dec d bl).
 auto.
 contradict n.
 assumption.
Qed.

Lemma Emptying_Piles_Correct2 : forall (d:cand) (bl: list cand) (p: cand -> list (list ballot)),
 not (In d bl) -> (fun c => if (cand_in_dec c bl) then [] else p (c)) d = p (d). 
Proof.
 intros.
 simpl.
 destruct (cand_in_dec d bl). 
 contradict H.
 assumption.
 reflexivity.
Qed.


Definition ACT_LH_transfer (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists nba t p np bl nbl h e,         (** transfer votes **) 
  prem = state ([], t, p, bl, e, h) /\ 
  (length (proj1_sig e) < st) /\
  (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\        (* and we can't elect any candidate *)
  exists l c,                          (* and there exists a list l and a candidate c *)
   (bl = c :: l /\                     (* such that c is the head of the backlog *)
   nbl = [] /\                          (* and the backlog is updated by removing the head c *)
   nba = fold_left (fun (acc: list ballot) => (fun (c: cand) => (acc ++ (flat_map (fun x => x) (p c))))) bl []
    /\ forall d, In d bl -> np(d) = [] /\                                (* and the new pile for c is empty *)
     (forall d, not (In d bl) -> np(d) = p(d))) /\    
   conc = state (nba, t, np, nbl, e, h).  

Lemma ACT_LH_Transfer_IsLegitimate : Is_Legitimate_Transfer ACT_LH_transfer.
Proof.
 intros.
 unfold Is_Legitimate_Transfer.
 split.
 intros.
 destruct H0 as [H1 [H2 H3]]. 
 exists (state 
         (fold_left (fun (acc: list ballot) => (fun (c: cand) => (acc ++ (flat_map (fun x => x) (p c))))) bl [],
         t, fun c => if (cand_in_dec c bl) then [] else (p c), [], e, h)).
 unfold ACT_LH_transfer.
 exists (fold_left (fun (acc: list ballot) => (fun (c: cand) => (acc ++ (flat_map (fun x => x) (p c))))) bl []).
 exists t. exists p. exists (fun c => if (cand_in_dec c bl) then [] else (p c)). exists bl. exists [].
 exists h. exists e. intuition.  
 specialize (list_nonempty_type cand bl H2). intro Hyp. destruct Hyp as [ head [tail Hyp1]].
 exists tail. exists head. intuition. 
 destruct (cand_in_dec d bl) as [i1 | i2]. reflexivity. contradict i2. assumption.
 destruct (cand_in_dec d0 bl) as [s1 | s2]. contradiction H4. auto.
 intros.
 unfold ACT_LH_transfer in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 exists nba.
 exists t. exists p. exists np.
 exists bl. exists []. exists h. exists e. intuition. destruct H3 as [tail [head [H31 H32]]].
 destruct H31 as [H311 H312].
 rewrite H311.
 simpl.
 omega.
 destruct H3 as [l [candid [H31 H32]]]. 
 intuition.
 rewrite H4 in H32.
 assumption.
Qed.

Definition ACTLH_STV := (mkSTV (quota)  
                         (Union_InitStep) (UnionInitStep_IsLegitimate) 
                         (Union_count) (UnionCount_IsLegitimate)
                         (ACT_LH_transfer) (ACT_LH_Transfer_IsLegitimate)
                          (Union_elect) (UnionElect_IsLegitimate)
                         (Union_elim) (UnionElim_IsLegitimate)
                          (Union_hwin) (UnionHwin_IsLegitimate)
                         (Union_ewin) (UnionEwin_IsLegitimate)).

Definition ACTLH_Termination := Termination (initial (Filter bs)) init_stages_R_initial ACTLH_STV.


(* transferring only the last parcel of the head of the backlog *)
Definition LastParcel_transfer (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists nba t p np bl nbl h e,         (** transfer votes **) 
  prem = state ([], t, p, bl, e, h) /\ 
  (length (proj1_sig e) < st) /\
  (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\        (* and we can't elect any candidate *)
  exists l c,                          (* and there exists a list l and a candidate c *)
   (bl = c :: l /\                     (* such that c is the head of the backlog *)
   nbl = l /\                          (* and the backlog is updated by removing the head c *)
   nba = last (p c) [] /\ np(c) = [] /\                                (* and the new pile for c is empty *)
     (forall d, d <> c -> np(d) = p(d))) /\    
   conc = state (nba, t, np, nbl, e, h).  

Lemma LastParcel_Transfer_IsLegitimate : Is_Legitimate_Transfer LastParcel_transfer.
Proof.
 unfold Is_Legitimate_Transfer. 
 split. 
 intros.
 destruct H0 as [H1 [H2 H3]].
 specialize (list_nonempty_type cand bl H2). intro Hyp. destruct Hyp as [head [tail Hyp1]].
 exists (state (last (p head) [], t, fun d => if (cand_eq_dec d head) then [] else (p d), tail, e, h)).  
 unfold LastParcel_transfer. exists (last (p head) []). exists t. exists p. 
 exists (fun d => if (cand_eq_dec d head) then [] else (p d)). 
 exists bl. exists tail. exists h. exists e. 
 intuition.
 exists tail. exists head.
 intuition.
 destruct (cand_eq_dec head head). reflexivity. contradict f. auto.
 destruct (cand_eq_dec d head). contradiction H0. reflexivity. 
 intros.
 unfold LastParcel_transfer in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 exists nba. exists t. exists p. exists np. exists bl. exists nbl. exists h. exists e.
 intuition. 
 destruct H14 as [l [candid H141]]. 
 destruct H141 as [H1411 H1412].
 destruct H1411 as [H3 [H4 H5]].
 rewrite H3. 
 rewrite H4.
 simpl.
 omega.
 destruct H14 as [tail [head [H141 H142]]].
 assumption.
Qed.

Definition LastParcelTrans_STV := 
                (mkSTV (quota)  
                       (Union_InitStep) (UnionInitStep_IsLegitimate) 
                       (Union_count) (UnionCount_IsLegitimate)
                       (LastParcel_transfer) (LastParcel_Transfer_IsLegitimate)
                       (Union_elect) (UnionElect_IsLegitimate)
                       (Union_elim) (UnionElim_IsLegitimate)
                       (Union_hwin) (UnionHwin_IsLegitimate)
                       (Union_ewin) (UnionEwin_IsLegitimate)).

Definition LastParcelTrans_Termination := 
        Termination (initial (Filter bs)) init_stages_R_initial LastParcelTrans_STV.

Definition Update_transVal (c: cand) (p: cand -> list (list ballot)) (t: cand -> Q) :=
 let Sum_parcel := sum (last (p c) []) in
  let r :=  (Qred ((Qred ((t c) - quota)) / Sum_parcel)) in
    match (Qlt_le_dec 0 Sum_parcel) with
       left _ => match (Qlt_le_dec r 1) with
                    left _ => r
                   |right _ => (1)%Q
                 end
       |right _ => (1)%Q
    end.

(* transfer value has changed so that only last parcel is to be transferred at a Manual_ACT rate*)
(* note that only the last parcel is kept after being updated. The rest of the parcel is thrown out! *)
Definition ManualACT_elect (prem: Machine_States) (conc: Machine_States) : Prop :=
 exists t p np (bl nbl: list cand) nh h (e ne: {l : list cand | length l <= st }),
    prem = state ([], t, p, bl, e, h) /\ 
    exists l,                                      
     (l <> [] /\                                  
     length l <= st - length (proj1_sig e) /\    
     (forall c, In c l -> In c (proj1_sig h) /\ (hd nty t (c) >= quota)%Q) /\      
     ordered (hd nty t) l /\ 
     Leqe l (proj1_sig nh) (proj1_sig h) /\          
     Leqe l (proj1_sig e) (proj1_sig ne) /\     
     (forall c, In c l -> ((np c) = map (map (fun (b : ballot) => 
         (fst b, (Qred (snd b * (Update_transVal c p (hd nty t))))%Q))) [(last (p c) [])])) /\  
     (forall c, ~ In c l -> np (c) = p (c)) /\  
     nbl = bl ++ l) /\                                 
  conc = state ([], t, np, nbl, ne, nh).      

Definition update_pile_ManualACT (p: cand -> list (list ballot)) (t: cand -> Q) (l: list cand) (q:Q) (c:cand):=   
 if cand_in_dec c l 
    then  
       map (map (fun (b : ballot) => 
         (fst b, (Qred (snd b * (Update_transVal c p t)))%Q))) [(last (p c) [])] 
    else (p c).

Lemma ManualACT_elect_IsLegitimate: Is_Legitimate_Elect ManualACT_elect.
Proof.
 intros.
 unfold Is_Legitimate_Elect.
 split.
 intros.
 unfold Union_elect.
 specialize (constructing_electable_first).  
 intro H1.
 destruct X as [c [X1 X2]].
 assert (Hyp: length (proj1_sig e) < st).
 omega.
 specialize (H1 e (hd nty t) h quota Hyp (proj2_sig h)).
 destruct H1 as [listElected H11].
 destruct H11 as [H111 [H112 [H113 [H114 H115]]]].
 specialize (Removel_nodup listElected (proj1_sig h) (proj2_sig h)). intro NoDupH.
 assert (Assum: length ((proj1_sig e) ++ listElected) <= st).
 rewrite app_length.
 omega.
 exists (state ([], t, fun c => update_pile_ManualACT p (hd nty t) listElected quota c, bl ++ listElected, 
 exist _ ((proj1_sig e) ++ listElected) Assum, exist _ (Removel listElected (proj1_sig h)) NoDupH)).
 exists t. exists p. exists (fun x => update_pile_ManualACT p (hd nty t) listElected quota x).
 exists bl. exists (bl ++ listElected). exists (exist _ (Removel listElected (proj1_sig h)) NoDupH).
 exists h. exists e. exists (exist _ ((proj1_sig e) ++ listElected) Assum). 
 split. auto.
 exists listElected.
 intuition.
 assert (NonEmptyElected: length listElected = 0). 
 rewrite H2.
 simpl. reflexivity.
 assert (VacantSeat: length (listElected) < st - (length (proj1_sig e))).
 rewrite app_length in Assum.
 rewrite NonEmptyElected in Assum.
 omega.
 specialize (H115 c). 
 intuition.
 rewrite H2 in H3.
 inversion H3.
 simpl.
 unfold Leqe.
 apply Permutation_App.
 apply (nodup_permutation).
 intros candid HypCand. 
 specialize (H111 candid HypCand).
 intuition.
 assumption. 
 apply (proj2_sig h).
 simpl.
 unfold Leqe.
 apply Permutation_refl.
 unfold update_pile_ManualACT.
 destruct (cand_in_dec c0 listElected).
 trivial.
 contradict f. assumption.
 unfold update_pile_ManualACT.
 destruct (cand_in_dec c0 listElected).
 contradict H2.
 assumption.
 auto.
 intros.
 unfold Union_elect in H.
 destruct H as [t [p [np [bl [nbl [nh [h [e [ne H1]]]]]]]]].
 exists t. exists p; exists np. exists bl. exists nbl. exists e. exists ne. exists nh. exists h. 
 destruct H1 as [H11 H12].
 destruct H12 as [l H121].
 intuition.
 unfold Leqe in H4.  
 specialize (Permutation_length H4). intro Permut_length.
 rewrite Permut_length.
 rewrite  app_length.
 specialize (list_nonempty_type cand l H1). intro.
 destruct X as [c [l' HX]].
 rewrite HX.
 simpl. 
 omega.
 unfold Leqe in H5.
 specialize (Permutation_length H5). intro.
 rewrite H8.
 rewrite app_length.
 specialize (list_nonempty_type cand l H1). intro.
 destruct X as [c [l' HX]]. 
 rewrite HX.
 simpl.
 omega.
Qed.

Definition ManualACT_STV := 
                (mkSTV (quota)  
                       (Union_InitStep) (UnionInitStep_IsLegitimate) 
                       (Union_count) (UnionCount_IsLegitimate)
                       (LastParcel_transfer) (LastParcel_Transfer_IsLegitimate)
                       (ManualACT_elect) (ManualACT_elect_IsLegitimate)
                       (Union_elim) (UnionElim_IsLegitimate)
                       (Union_hwin) (UnionHwin_IsLegitimate)
                       (Union_ewin) (UnionEwin_IsLegitimate)).

Definition ManualACT_Termination := 
        Termination (initial (Filter bs)) init_stages_R_initial ManualACT_STV.
*)
*)

(*End Base.*)

End B.

(*Module M := B Instantiation.*)

(*
Extraction Language Haskell.
Extraction "Lib.hs" Act_Termination.
*)
(*Extraction "Lib.hs" Union_Termination.*)

(*
Extraction Language Haskell.
Extraction "Lib.hs" ManualACT_Termination. 
*)

(*
Extraction Language Haskell.
Extraction "Lib.hs" LastParcelTrans_Termination.
*)

(*
Extraction Language Haskell.
Extraction "Lib.hs" ACTLH_Termination. 
*)


(* Extraction Language Haskell.
Extraction "Lib.hs" Union_Termination. *)

 
