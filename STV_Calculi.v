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
Import ListNotations.

(* notation for type level existential quantifier *)
Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

(* Section genericTermination.
Close Scope Q_scope. *) 
 
Section STV_Framework.
Close Scope Q_scope. 

Variable cand: Type.
Variable cand_all: list cand.
Hypothesis cand_nodup: NoDup cand_all.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.
Hypothesis cand_in_dec: forall c : cand, forall l : list cand, {In c l} + {~In c l}.

(* a ballot is a permutation of the list of candidates and a transfer balue *)
Definition ballot :=  ({v : list cand | (NoDup v) /\ ( [] <> v)} * Q).

Variable bs : list ballot.
Variable st : nat. 
Variable quota : Q.
Definition length_empty: length ([]:list cand) <= st.
Proof.
 simpl.
 induction st.
 auto.
 auto.
Defined.

Definition nbdy : list cand := [].                    (* empty candidate list *)
Definition nty  : cand -> Q := fun x => (0)%Q .          (* null tally *)
Definition nas  : cand -> list (list ballot) := fun x => []. (* null vote assignment *)
Definition emp_elec : {l: list cand | length l <= st} := 
 exist _ ([] :list cand) length_empty.                (*empty list of elected candidates*)



Definition all_hopeful : {hopeful: list cand | NoDup hopeful} := 
 exist _ cand_all cand_nodup.           (*inintial list of all candidates*)



(* summation of weights in a list of ballots *)
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

Fixpoint is_elem (l:list cand) (c :cand) :=
 match l with
           [] => false
           |l0::ls => if cand_eq_dec l0 c then true else is_elem ls c
 end.

(*checks if list l has duplicate elements*)
Fixpoint nodup_elem (l:list cand) :=
 match l with
          [] => true
          |l0::ls => if is_elem ls l0 
                       then false
                     else nodup_elem ls      
 end. 

Fixpoint non_empty (l:list cand):=
 match l with 
         [] => false
         |_ => true
 end.

(*filters ballots so that only formal ballots remain*)
Fixpoint Filter (l: list ballot):=
 match l with
         [] => []
         |l0::ls => if nodup_elem (proj1_sig (fst l0))
                       && (non_empty (proj1_sig (fst l0)))
                         then l0:: Filter ls
                    else Filter ls  
 end.

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
 assert ( {(f x < (f l))%Q}  + {((f l) <= (f x))%Q}).
 apply (Qlt_le_dec (f x) (f l))%Q.
 assert ( {(f x <= (f l))%Q}  + {((f l) <= (f x))%Q}).
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
 assert ({ (f a < f x)%Q} + {(f x <= f a)%Q}).
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

(* initial, intermediate and final states in vote counting *)
Inductive FT_Judgement :=
 initial:
     list ballot -> FT_Judgement 
 |state:                                   (** intermediate states **)
    list ballot                            (* uncounted votes *)
    * list (cand -> Q)                          (* tally *)
    * (cand -> list (list ballot))                (* pile of ballots for each candidate*)
    * list cand                            (* backlog of candidates requiring transfer *)
    * {elected: list cand | length  elected <= st}            (* elected candidates no longer in the running *)
    * {hopeful: list cand | NoDup hopeful}                    (* hopeful candidates still in the running *)
 
      -> FT_Judgement
 | winners:                                                   (** final state **)
      list cand -> FT_Judgement.                              (* election winners *)

 
Definition FT_final (a : FT_Judgement) : Prop :=
 exists w, a = winners (w).

Definition FT_initial (a : FT_Judgement) : Prop :=
 exists (ba : list ballot), a = initial (ba).

Lemma final_dec: forall j : FT_Judgement, (FT_final j) + (not (FT_final j)).
Proof. 
 intro j. 
  destruct j;
   repeat (right;unfold FT_final;unfold not;intro H;destruct H;discriminate) 
     || 
       left;unfold FT_final;exists l;reflexivity.
Defined.

Lemma initial_dec: forall j: FT_Judgement, (FT_initial j) + not (FT_initial j).
Proof.
 intro j.
  destruct j;
    repeat (left;unfold FT_initial;exists l;reflexivity)
        ||
          (right;intro H;inversion H; discriminate).
Qed.        
 

(* Rules *)
Definition FT_Rule := FT_Judgement -> FT_Judgement -> Prop.

(* well founded order *)
Definition FT_WFO := nat * (nat * (nat * nat)). 

Definition dep2 := sigT (A:= nat) (fun a => nat).
Definition dep3 := sigT (A:= nat) (fun a => dep2).
Definition dep4 := sigT (A:= nat) (fun a => dep3).
Definition mk2  : nat * nat -> dep2.
 intros (p,q).
 exists p.
 exact q.
 Defined.

Definition mk3 : nat * (nat * nat) -> dep3.
 intros (n, p_q).
 exists n.
 exact (mk2 p_q).
Defined. 

Definition mk4 : nat * (nat * (nat * nat)) -> dep4.
 intros (m, n_p_q).
 exists m.
 exact (mk3 n_p_q).
Defined.

Definition lt_pq :dep2->dep2->Prop :=
  (lexprod nat (fun a => nat) Peano.lt (fun a:nat =>Peano.lt)).

Definition lt_npq : dep3 -> dep3 -> Prop :=
  (lexprod nat (fun a => dep2) Peano.lt (fun a:nat =>lt_pq)).
Definition lt_mnpq : dep4 -> dep4 -> Prop:=
  (lexprod nat (fun a => dep3) Peano.lt (fun (a:nat) => lt_npq)).

Lemma wf_Lexprod1 : well_founded lt_npq.
 unfold lt_npq. apply wf_lexprod.
 apply lt_wf.
 intro n.
 unfold lt_pq;apply wf_lexprod.
 apply lt_wf.
 intro m; apply lt_wf.
Qed.

(*lt_mnpq is a well founded ordering*)
Lemma wf_Lexprod : well_founded lt_mnpq.
Proof.
 red in |-*;apply wf_lexprod. apply lt_wf. intro n.
 red in |-*;apply wf_lexprod. apply lt_wf. intro m.
 red in |-*;apply wf_lexprod. apply lt_wf. intro p.
 apply lt_wf.
Qed.

(*imposing an ordering on judgements*)
Definition FT_wfo : FT_WFO -> FT_WFO -> Prop := (fun x y : nat * (nat * (nat * nat)) => 
 lt_mnpq (mk4 x) (mk4 y)).

Lemma FT_wfo_wf : well_founded FT_wfo.
 unfold FT_wfo. 
 apply wf_inverse_image.
 apply wf_Lexprod.
Qed.

(* measure function maps to ({0,1},length h, length bl, length ba) *)
Definition FT_m: { j: FT_Judgement | not (FT_final j) } -> FT_WFO.
 intro H. 
 destruct H as [j ej]. 
 destruct j.
 split. 
 exact 1.
 split.
 exact 0. split. exact 0. exact 0.
 destruct p as [[[[[ba t] p] bl] e] h].
 split.
 exact 0.
 split.
 exact (length (proj1_sig h)).
 split.
 exact (length bl).
 exact (length ba).
 contradiction ej.
 unfold FT_final. 
 exists l.
 reflexivity.
Defined.

(* lexicographic order behaves as expected *)
Lemma wfo_aux:  forall a b c d a' b' c' d' : nat,
 (lt_mnpq (mk4 (a, (b, (c,d)))) (mk4 (a', (b', (c',d')))) <->
   (a < a' \/
   (a = a' /\ b < b' \/
   (a = a' /\ b = b' /\ c < c' \/
   (a = a' /\ b = b' /\ c = c' /\ d < d'))))).
Proof.
 intros. split. unfold lt_mnpq. unfold mk4. simpl. intro H. inversion H. subst.
  (* case 1st component are below one another *)
 auto.
  (* case 1st components are equal *)
 unfold lt_npq in H1. inversion H1. subst. auto.
  (* case 1st and 2nd components are equal and 3rd are below one another *)
  unfold lt_pq in H6.
  inversion H6.
  right;right;left;auto.
  (* case where the first three components are equal but the last decreases*) 
  right;right;right;auto.        
  (* right-to-left direction *)
 intro H. destruct H.
  (* case 1st components are below one another *)
 unfold lt_mnpq. apply left_lex. assumption.
 destruct H.
  (* case 1st components are equal and 2nd components are below one another *)
 destruct H as [H1 H2]. subst. apply right_lex. apply left_lex. assumption.
  (* case 1st and 2nd components are identical, and 3rd components are below one another *)
 destruct H as [H1 | H2]. destruct H1 as [H11 [H12 H13]]. subst. repeat apply right_lex || apply right_lex || apply left_lex. assumption. destruct H2 as [H21 [H22 [H23 H24]]]. subst. repeat apply right_lex. assumption.
Qed.

Definition mk_nfj: forall j: FT_Judgement, forall e: not (FT_final j), { j : FT_Judgement | not (FT_final j) }.
  intros j e. exists j. assumption.
Defined.

Definition Is_Legitimate_Initial (R : FT_Judgement -> FT_Judgement -> Prop) :=  
  (forall premise, forall ba, (premise = initial ba) -> existsT conclusion,
     (conclusion = state (Filter ba, [nty], nas, nbdy, emp_elec, all_hopeful)) *  
      R premise conclusion) * 
  (forall p c, R p c -> exists ba ba' t ass bl e h, (p = initial ba) /\ (c = state (ba', t, ass, bl, e, h))).

Definition Is_Legitimate_Count (R: FT_Judgement -> FT_Judgement -> Prop) :=
 (forall premise, forall ba t p  bl h e, (premise = state (ba, t, p ,bl ,e, h)) -> (ba <> []) ->
    existsT conclusion, (R premise conclusion)) *
 (forall (p: FT_Judgement) (c: FT_Judgement), R p c -> exists ba1 ba2 t1 t2 p1 p2 bl e h, 
   (p = state (ba1, t1, p1, bl, e, h)) /\ 
   (c = state (ba2, t2 :: t1, p2, bl, e, h)) /\ 
   ( length ba2 < length ba1)).

(* note that I have put the null tally as the default value for head in case of empty list *)
Definition Is_Legitimate_Transfer (R: FT_Judgement -> FT_Judgement -> Prop) :=
 (forall premise, forall t p bl e h, (premise = state ([], t, p, bl, e, h)) ->
   (length (proj1_sig e) < st) /\ (bl <> []) /\
   (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) -> existsT conc, R premise conc) *
 (forall premise conclusion, R premise conclusion ->
   exists nba t p np bl nbl h e,
   (premise = state ([], t, p, bl, e, h)) /\
   (length nbl < length bl) /\
   (conclusion = state (nba, t, np, nbl, e, h))). 

Definition Is_Legitimate_Elect (R: FT_Judgement -> FT_Judgement -> Prop) :=
 (forall premise, forall t p bl e h, (premise = state ([], t, p, bl, e, h)) ->
     (existsT (c: cand), 
     (length (proj1_sig e)) + 1 <= st /\  
     In c (proj1_sig h) /\ ((hd nty t) (c) >= quota)%Q) -> existsT conc, R premise conc) *
 (forall premise conclusion, R premise conclusion ->
     exists 
     t p np bl nbl e ne nh h, 
     (premise = state ([], t, p, bl, e, h)) /\
          (length (proj1_sig nh) < length (proj1_sig h)) /\
          (length (proj1_sig e) < length (proj1_sig ne)) /\
     (conclusion = state ([], t, np, nbl, ne, nh))).

Definition Is_Legitimate_Elim (R: FT_Judgement -> FT_Judgement -> Prop) :=
  (forall premise, forall t p e h, (premise = state ([], t, p, [], e, h)) ->
     length (proj1_sig e) + length (proj1_sig h) > st /\
     (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) -> existsT conc, R premise conc) * 
  (forall premise conclusion, R premise conclusion ->
     exists nba t p np e h nh,
     (premise = state ([], t, p, [], e, h)) /\
     length (proj1_sig nh) < length (proj1_sig h) /\
     (conclusion = state (nba, t, np, [], e, nh))).

Definition Is_Legitimate_Hwin (R: FT_Judgement -> FT_Judgement -> Prop) :=
  (forall premise, forall ba t p bl e h, (premise = state (ba, t, p, bl, e, h)) ->
     length (proj1_sig e) + (length (proj1_sig h)) <= st -> existsT conc, R premise conc) *
  (forall premise conclusion, R premise conclusion ->
     exists w ba t p bl e h,
      (premise = state (ba, t, p, bl, e, h)) /\ 
      w = (proj1_sig e) ++ (proj1_sig h) /\ 
      (conclusion = winners w)).

Definition Is_Legitimate_Ewin (R: FT_Judgement -> FT_Judgement -> Prop) :=
 (forall premise, forall ba t p bl e h, (premise = state (ba, t, p, bl, e, h)) ->
    length (proj1_sig e) = st -> existsT conc, R premise conc) *
 (forall premise conclusion, R premise conclusion ->
    exists w ba t p bl e h,
    (premise = state (ba, t, p, bl, e, h)) /\
     w = (proj1_sig e) /\ 
    (conclusion = winners (proj1_sig e))).

Record STV := 
   mkSTV {qu: Q;
          initStep: FT_Judgement -> FT_Judgement -> Prop;
          evidence_initStep: (Is_Legitimate_Initial initStep);
          count: FT_Judgement -> FT_Judgement -> Prop;
          evidence_count: (Is_Legitimate_Count count);    
          transfer: FT_Judgement -> FT_Judgement -> Prop;
          evidence_transfer: (Is_Legitimate_Transfer transfer);
          elect: FT_Judgement -> FT_Judgement -> Prop;
          evidence_elect: (Is_Legitimate_Elect elect);
          elim: FT_Judgement -> FT_Judgement -> Prop;
          evidence_elim: (Is_Legitimate_Elim elim);
          hwin: FT_Judgement -> FT_Judgement -> Prop;
          evidence_hwin: (Is_Legitimate_Hwin hwin);
          ewin: FT_Judgement -> FT_Judgement -> Prop;
          evidence_ewin: (Is_Legitimate_Ewin ewin)}.

(* beginning of measure decreasing proof for new formalised rules*)
Lemma dec_Initial : forall (s: STV) (p c : FT_Judgement),
 initStep s p c  -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof. 
 intros s p c H ep ec.
 destruct s. 
 simpl in H.
 unfold Is_Legitimate_Initial in evidence_initStep0.
 destruct p.
 destruct c.
 destruct evidence_initStep0 as [Hev1 Hev2].
 specialize (Hev2 (initial l) (initial l0)).
 intuition.
 destruct H0 as [ba [ba' [t [ass [bl [e [h [Hev21 Hev22]]]]]]]].
 inversion Hev22. 
 destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite wfo_aux.
 left;auto.
 contradict ec. unfold FT_final. exists l0. reflexivity.
 destruct evidence_initStep0 as [Hev1 Hev2].
 specialize (Hev2 (state p) c).
 intuition.
 destruct H0 as [ba [ba' [t [ass [bl [e1 [h1 [Hev21 Hev22]]]]]]]].
 inversion Hev21.
 contradict ep. unfold FT_final. exists l. auto.
Qed.

Lemma dec_Count : forall (s: STV) (p c : FT_Judgement),
 count s p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s. 
 simpl in Hr.
 unfold Is_Legitimate_Count in evidence_count0.
 destruct evidence_count0 as [Hev1 Hev2].
 specialize (Hev2 p c Hr).
 destruct Hev2 as [ba1 [ba2 [t1 [t2 [p1 [p2 [e [h [Hev21 [Hev22 Hev23]]]]]]]]]].
 destruct p.
 inversion Hev22. 
 destruct c.
 destruct Hev23 as [Hev231 Hev232].
 inversion Hev231.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p0 as [[[[[ba22 t22] p22] bl22] e22] h22].
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 inversion Hev22. destruct Hev23 as [Hev231 Hev232]. inversion Hev231. subst. 
 right. right. right.
 split;auto.
 contradict ec.
 unfold FT_final. exists l. reflexivity.
 contradict ep. exists l. auto.
Qed.

Lemma dec_Transfer : forall (s: STV) (p c : FT_Judgement),
 transfer s p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s. 
 simpl in Hr.
 unfold Is_Legitimate_Transfer in evidence_transfer0.
 destruct evidence_transfer0 as [Hev1 Hev2].
 specialize (Hev2 p c Hr).
 destruct Hev2 as [nba [t [p0 [np [bl [nbl [h [e [Hev21 [Hev22 Hev23]]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev21. inversion Hev23. subst.
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 right; right;left. auto.
 contradict ec; unfold FT_final; exists l ;auto.
 contradict ep; exists l; auto.
Qed.

Lemma dec_Elect : forall (s: STV) (p c : FT_Judgement),
 elect s p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold Is_Legitimate_Elect in evidence_elect0.
 destruct evidence_elect0 as [Hev1 Hev2].
 specialize (Hev2 p c Hr).
 destruct Hev2 as [t [p0 [np [bl [nbl [e [ne [nh [h [Hev21 [Hev22 [Hev23 Hev24]]]]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev24.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev21. inversion Hev24. subst.
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 right; left. auto.
 contradict ec; exists l; reflexivity.
 contradict ep; exists l; auto.
Qed.

Lemma dec_Elim : forall (s: STV) (p c : FT_Judgement),
 elim s p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold Is_Legitimate_Elim in evidence_elim0.
 destruct evidence_elim0 as [Hev1 Hev2].
 specialize (Hev2 p c Hr).
 destruct Hev2 as [nba [t [p0 [np [e [h [nh [Hev21 [Hev22 Hev23]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 destruct p as [[[[[ba11 t11] p11] bl11] e11] h11].
 destruct p1 as [[[[[ba22 t22] p22] bl22] e22] h22].
 inversion Hev21. inversion Hev23. subst.
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite wfo_aux.
 right;left. auto.
 contradict ec; exists l; reflexivity.
 contradict ep; exists l; auto.
Qed.

Lemma dec_Hwin  : forall (s: STV) (p c : FT_Judgement),
 hwin s p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold Is_Legitimate_Hwin in evidence_hwin0.
 destruct evidence_hwin0 as [Hev1 Hev2].
 specialize (Hev2 p c Hr).
 destruct Hev2 as [w [ba [t [p0 [bl [e [h [Hev21 [Hev22 Hev23]]]]]]]]].
 destruct p.
 inversion Hev21.
 destruct c.
 inversion Hev23.
 inversion Hev23.
 contradict ec; exists l; reflexivity.
 contradict ep; exists l; auto.
Qed.

Lemma dec_Ewin : forall (s: STV) (p c : FT_Judgement),
 ewin s p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj c ec))
  (FT_m (mk_nfj p ep)).
Proof.
 intros s p c Hr ep ec.
 destruct s.
 simpl in Hr.
 unfold Is_Legitimate_Ewin in evidence_ewin0.
 destruct evidence_ewin0 as [Hev1 Hev2].
 specialize (Hev2 p c Hr).
 destruct Hev2 as [w [ba [t [p0 [e [h [Hev21 [Hev22 [Hev23 Hev24]]]]]]]]].
 destruct p.
 inversion Hev21.
 inversion Hev22.
 destruct c.
 inversion Hev24.
 inversion Hev24.
 contradict ec; exists l; auto.
 contradict ep; exists l; auto.
Qed.
 
Lemma measure_dec : forall (s: STV) (p c: FT_Judgement), (initStep s p c) \/ (count s p c) \/ 
    (elect s p c) \/ (transfer s p c) \/ (elim s p c) \/ (hwin s p c) \/ (ewin s p c) -> 
    forall (ep : ~ FT_final p) (ec: ~ FT_final c), FT_wfo (FT_m (mk_nfj c ec)) (FT_m (mk_nfj p ep)).   
Proof.
 intros s p c H ep ec.
 destruct H.
 apply (dec_Initial s p c H ep ec).
 destruct H.
 apply (dec_Count s p c H ep ec).
 destruct H.
 apply (dec_Elect s p c H ep ec).
 destruct H.
 apply (dec_Transfer s p c H ep ec).
 destruct H.
 apply (dec_Elim s p c H ep ec).
 destruct H.
 apply (dec_Hwin s p c H ep ec).
 apply (dec_Ewin s p c H ep ec).
Qed.

(*end of measure decreasing proof for new formalised rules*)
(* start: Certificate st bs s (state (Filter bs, [nty], nas, [], 
                                    emp_elec,all_hopeful)) *)


Inductive Certificate (st: nat) (bs: list ballot) (s: STV) (j0: FT_Judgement): FT_Judgement -> Type:=
   start:  forall j, (j = j0) -> Certificate st bs s j0 j
 | appInit: forall j1 j2, Certificate st bs s j0 j1 -> initStep s j1 j2 -> Certificate st bs s j0 j2 
 | appCount: forall j1 j2, Certificate st bs s j0 j1 -> count s j1 j2 -> Certificate st bs s j0 j2   
 | appElect: forall j1 j2, Certificate st bs s j0 j1 -> elect s j1 j2 -> Certificate st bs s j0 j2
 | appTrans: forall j1 j2, Certificate st bs s j0 j1 -> transfer s j1 j2 -> Certificate st bs s j0 j2
 | appElim: forall j1 j2, Certificate st bs s j0 j1 -> elim s j1 j2 -> Certificate st bs s j0 j2 
 | appHwin: forall j1 j2, Certificate st bs s j0 j1 -> hwin s j1 j2 -> Certificate st bs s j0 j2
 | appEwin: forall j1 j2, Certificate st bs s j0 j1 -> ewin s j1 j2 -> Certificate st bs s j0 j2.

Lemma Rule_Application : forall (s: STV) (j1: FT_Judgement), ~ (FT_final j1) -> 
                   existsT j2, {initStep s j1 j2} + {count s j1 j2} + {elect s j1 j2} + 
                              {transfer s j1 j2} + {elim s j1 j2} + {hwin s j1 j2} + {ewin s j1 j2}. 
Proof.
 intros s j1 H.
 destruct s.
 destruct j1.
 simpl.
 unfold Is_Legitimate_Initial in  evidence_initStep0.
 destruct evidence_initStep0 as [HevInit1 HevInit2]. 
 specialize (HevInit1 (initial l) l (eq_refl)).
 destruct HevInit1 as [conc [H11 H12]].
 exists conc.
 left; left; left; left; left;left. auto.
 simpl.
 destruct p as [[[[[ba t] pile] bl] e] h].
 specialize (lt_eq_lt_dec (length (proj1_sig e)) st). intro LenElected.
 (* examining if we have filled all seats *)
 destruct LenElected as [LenElected1 | LenElected2]. 
 destruct LenElected1 as [LenElected11 | LenElected12].
 (* the case where there are seats to fill *)
 specialize (le_gt_dec (length (proj1_sig e) + length (proj1_sig h)) st). intro LenElectedHopeful.
 (* examining the length of elected and hopeful togather *)
 destruct LenElectedHopeful as [LenElectedHopeful1 | LenElectedHopeful2]. 
 (* the case where len (e ++ h) <= st *)
 destruct evidence_hwin0 as [HevHwin1 HevHwin2].
 specialize (HevHwin1 (state (ba, t, pile, bl, e, h)) ba t pile bl e h  (eq_refl) LenElectedHopeful1).
 destruct HevHwin1 as [conc HevHwin11]. 
 exists conc.
 left. right. assumption.
 (* the case where are more elected and hopeful than seats and less elected than seats*)
 destruct ba. 
 assert (([]<> (proj1_sig h)) -> 
       existsT d, In d (proj1_sig h) /\  (forall d', In d' (proj1_sig h) -> 
       ((hd nty t) d' <= (hd nty t) d)%Q)) by
           apply (list_max_cor cand (proj1_sig h) (hd nty t)).
 assert (forall (q:Q), ((forall c, In c (proj1_sig h) -> 
   ((hd nty t)(c) < q)%Q) + (existsT c: cand, In c (proj1_sig h) /\ ((hd nty t) (c) >= q)%Q))). 
 induction (proj1_sig h).
 intro q0.
 left; intros. contradict H0.
 assert (forall a: cand, forall h : list cand, [] <> a::h).
 intros.
 intro.
 inversion H0.
 specialize (X (H0 a l)).
 destruct X.
 destruct a0.
 assert (forall (q1: Q), ({((hd nty t) x < q1)%Q} + {(q1 <= (hd nty t) x)%Q})).
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
 specialize (X0 quota).
 destruct X0.
 destruct bl.
 assert ((proj1_sig h) <> []).
 specialize (list_min cand (proj1_sig h) (hd nty t)).
 intro.
 destruct X0.
 destruct (proj1_sig h).
 simpl in LenElectedHopeful2. 
 omega.
 inversion e0.
 destruct s.
 destruct a. 
 intro. rewrite H2 in H0. inversion H0.
 (* the case for elimination *)
 destruct evidence_elim0 as [HevElim1 HevElim2].
 specialize (HevElim1 (state ([], t, pile, [], e, h)) t pile e h (eq_refl)).
 intuition. 
 destruct X0 as [conc Hconc].
 exists conc.
 left; left; right. auto.
 (* the case of transfer *)
 destruct evidence_transfer0 as [Hevtrans1 Hevtrans2].
 specialize (Hevtrans1 (state ([], t, pile, c::bl, e, h)) t pile (c::bl) e h).
 intuition.
 assert (Hyp: c:: bl = [] -> False). intro Hyp1. inversion Hyp1. 
 intuition.
 destruct X1 as [conc X31].
 exists conc. 
 left; left; left; right. assumption.
 (* the case for electing *)
 destruct evidence_elect0 as [HevElect1 HevElect2].
 specialize (HevElect1 (state ([], t, pile, bl, e, h)) t pile bl e h (eq_refl)).
 destruct s as [c s1].
 assert (HypE2: existsT c, (length (proj1_sig e)) + 1 <= st /\ (In c (proj1_sig h)) 
                                                           /\ (quota <= (hd nty t) c)%Q). 
 exists c.
 split. omega. 
 auto.
 specialize (HevElect1 HypE2).
 destruct HevElect1 as [conc HevElect21]. 
 exists conc.
 left; left; left; left; right. assumption.
 (* the case for count application *)
 destruct evidence_count0 as [HevCount1 HevCount2]. 
 specialize (HevCount1 (state (b ::ba, t, pile, bl, e, h)) (b::ba) t pile bl h e (eq_refl)).
 assert (HyCount: (b:: ba) <> []). intro. inversion H0.
 specialize (HevCount1 HyCount). 
 destruct HevCount1 as [conc HevCount].
 exists conc.
 left; left; left; left; left; right. auto.
 (* the case for ewin *)
 destruct evidence_ewin0 as [HevEwin1 HevEwin2].
 specialize (HevEwin1 (state (ba, t, pile, bl, e, h)) ba t pile bl e h  (eq_refl)). 
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


Lemma Extending_Certificate : 
  forall (s: STV),
  forall j0 j1, forall (ej0: ~ FT_final j0) (ej1: ~ FT_final j1), Certificate st bs s j0 j1 ->
    existsT j2, 
        (Certificate st bs s j0 j2) * 
        (forall ej2: (~ FT_final j2), FT_wfo (FT_m (mk_nfj j2 ej2)) (FT_m (mk_nfj j1 ej1))).                     
Proof.
 intros s j0 j1 ej0 ej1 H0.
 specialize (Rule_Application s j1 ej1). intro H1.
 destruct H1 as [conc H11].
 destruct H11 as [LH11 | RH11]. 
 destruct LH11 as [LLH11 | RLH11].
 destruct LLH11 as [LLLH11 | RLLH11]. 
 destruct LLLH11 as [LLLLH11 | RLLLH11].
 destruct LLLLH11 as [LLLLLH11 | RLLLLH11].
 destruct LLLLLH11 as [L6H11 | RL5H11].
 exists conc.
 split.
 apply (appInit st bs s j0 j1). assumption. auto.
 intro evconc. 
 apply (dec_Initial s j1 conc L6H11). 
 exists conc. 
 split.
 apply (appCount st bs s j0 j1). assumption. auto.
 apply (dec_Count s j1 conc RL5H11).
 exists conc.
 split.
 apply (appElect st bs s j0 j1). assumption. auto.
 apply (dec_Elect s j1 conc RLLLLH11). 
 exists conc. 
 split. 
 apply (appTrans st bs s j0 j1).  assumption. auto.
 apply (dec_Transfer s j1 conc RLLLH11).
 exists conc.
 split.
 apply (appElim st bs s j0 j1). assumption. auto.
 apply (dec_Elim s j1 conc RLLH11). 
 exists conc.
 split.
 apply (appHwin st bs s j0 j1). assumption. auto.
 apply (dec_Hwin s j1 conc RLH11).
 exists conc.
 split.
 apply (appEwin st bs s j0 j1). assumption. auto.
 apply (dec_Ewin s j1 conc RH11). 
Qed.

Lemma Termination_Aux : 
  forall (s: STV), 
  forall n: FT_WFO, 
  forall j0 (evj0: ~ FT_final j0),
  forall j (evj: not (FT_final j)), FT_m (mk_nfj j evj) = n -> 
        Certificate st bs s j0 j -> 
           existsT j', (FT_final j') * (Certificate st bs s j0 j').
Proof.                                                
 intros s n j0 evj0. 
 induction n as [w IH] using (well_founded_induction_type FT_wfo_wf).
 intros j evj Eqn Certj.
 assert (Hex: existsT j', 
   (Certificate st bs s j0 j') * 
   (forall evj' : not (FT_final j'), FT_wfo (FT_m (mk_nfj j' evj')) (FT_m (mk_nfj j evj)))).  
 apply (Extending_Certificate s j0 j evj0 evj Certj). 
 destruct Hex as [j' [Hex1 Hex2]].
 destruct (final_dec j') as [f | nf].
 exists j'. split. assumption. auto.
 specialize (Hex2 nf).
 rewrite <- Eqn in IH.
 destruct (IH (FT_m (mk_nfj j' nf)) Hex2 j' nf) as [j'' Hj''].
 reflexivity.  
 assumption.
 exists j''.
 auto.
Qed.

Theorem Termination : forall j0 (evj0: ~FT_final j0), forall (s: STV), 
                            existsT j, (FT_final j) * (Certificate st bs s j0 j).
Proof.
 intros j0 evj0 s.
 destruct (final_dec j0) as [f | ea].
 (*destruct (final_dec (state (Filter bs, [nty], nas, [], 
                                    emp_elec,all_hopeful))) as [f | ea].*)
 (*exists (state (Filter bs, [nty], nas, [], 
                                    emp_elec,all_hopeful)). *)
 contradict evj0.
 assumption.
 apply (Termination_Aux s (FT_m (mk_nfj j0 ea)) j0 ea j0 ea).  
 reflexivity.
 apply start. auto.
Qed. 

(* End STV_Framework.

Section Union_STV.
Close Scope Q_scope.*)

(* relation for `first continuing candidate' on a ballot in the list of ballots requiring attention *)
Definition fcc (ba : list ballot) (h : list cand) (c : cand) (b : ballot): Prop := 
  In (proj1_sig (fst b)) ((map (fun (d:ballot) => (proj1_sig (fst d)))) ba) /\
  In c h /\
  (exists l1 l2 : list cand, 
      proj1_sig (fst b) = l1 ++ [c] ++ l2 /\ 
      forall d, (In d l1 -> ~(In d h))).

(*checks if no cadidate whose name is in h, does not precede the candidate c in the list l*)
Fixpoint is_first_hopeful (c:cand) (h: list cand) (l : list cand):=
 match l with
          [] => false
          |l0::ls =>  if (cand_in_dec c h) then
                                               if cand_eq_dec l0 c then true 
                                               else                     
                                                   if cand_in_dec l0 h then false
                                                   else is_first_hopeful c h ls
                      else false  
 end. 



(*collects all of the ballots where c is the first continuing preference*)
Fixpoint list_is_first_hopeful (c:cand) (h: list cand) (ba: list ballot):=
 match ba with
          [] => []
          |b0::bas => if (is_first_hopeful c h (proj1_sig (fst b0))) 
                         then b0::(list_is_first_hopeful c h bas)
                      else (list_is_first_hopeful c h bas)        
 end.

Fixpoint List_IsFirst_Hopeful (c: cand) (h :list cand) (acc: list ballot) (ba: list ballot) :=
 match ba with
         [] => acc
        |b0 :: bas => if is_first_hopeful c h (proj1_sig (fst b0))
                        then List_IsFirst_Hopeful c h (b0 :: acc) bas
                      else List_IsFirst_Hopeful c h acc bas
 end.

(*every ballot b which c is its first preference, is an elements of the uncounted ballots ba, so that ballots are not assigned to a cadidate from an illegal source*) 
Lemma weakened_is_first_hopeful_ballot: forall c h ba, forall (d:ballot), In (proj1_sig (fst d)) (map (fun (d0:ballot) => (proj1_sig (fst (d0)))) (list_is_first_hopeful c h ba)) -> In (proj1_sig (fst d)) (map (fun (d: ballot) => (proj1_sig (fst d))) ba).
Proof.
 intros.
 induction ba.
 simpl in H.
 inversion H.
 specialize (list_eq_dec (cand_eq_dec) (proj1_sig (fst d)) (proj1_sig (fst a))).
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

Lemma nonempty_list_notempty: forall l1 l2 (c:cand), [] <> l1++[c]++l2.
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
 destruct (cand_eq_dec d0 a).
 simpl.
 destruct (cand_in_dec c h) as [CandInDec1 |CandInDec2].
 destruct (cand_eq_dec a c) as [i | j].
 rewrite i in H3.
 inversion H3.
 assert (Hypo: In c (l1++c::l2)).
 intuition.
 contradiction H4.
 destruct (cand_in_dec a h) as [p |q].
 auto.
 rewrite e in H2.
 contradiction q.  auto.
 simpl.
 destruct (cand_in_dec c h) as [CandInDec1 | CandInDec2].
 destruct (cand_eq_dec a c) as [i' | j'].
 rewrite i' in H3.
 inversion H3.
 exfalso.
 apply H4.
 intuition.
 destruct (cand_in_dec a h) as [p' |q'].
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
Lemma first_hopeful_true: forall c (h: {hopeful: list cand | NoDup hopeful}) (b:ballot) (ba: list ballot) l1 l2,(forall d, In d l1 -> ~ In d (proj1_sig h)) /\ (exists (d:ballot), (proj1_sig (fst d)) = l1++[c]++l2) /\ (In c (proj1_sig h)) -> is_first_hopeful c (proj1_sig h) (l1++[c]++l2) = true.
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
 destruct (cand_in_dec c (proj1_sig h)) as [CandInDec1 | CandInDec2].
 destruct (cand_eq_dec c c) as [i1 |i2].
 auto.
 contradiction i2.
 auto.
 contradiction CandInDec2.
 simpl.
 destruct (cand_in_dec c (proj1_sig h) ) as [CandInDec3 | CandInDec4].
 destruct (cand_in_dec a (proj1_sig h)).
 specialize (H11 a).
 assert (Hypo: In a (a::l1)).
 left;auto.
 specialize (H11 Hypo).
 contradiction H11.
 destruct (cand_eq_dec a c) as [CandEqDec1 |CandEqDec2].
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
 exists ((exist _ (l1++[c]++l2) Hypo4), (1)%Q).
 simpl.
 auto.
 inversion Hypo1.
 simpl;assumption.
 specialize (nonempty_list_notempty l1 l2 c);intro Hypo6;auto.            
 contradiction CandInDec4.
Qed.

(*c receives all of the ballots that prefer him as their first contiuing choice*)
Lemma fcc_listballot: forall ba (h: {hopeful: list cand | NoDup hopeful}),(forall c, forall d: ballot,  fcc ba (proj1_sig h) c d -> In (proj1_sig (fst d)) (map (fun (d0:ballot) => (proj1_sig (fst d0))) (list_is_first_hopeful c (proj1_sig h) ba))).
Proof.
 intros ba h c.
 intros d H4.
 unfold fcc in H4.
 destruct H4 as [H4_1 [H4_2 [l1 [l2 [H4_3 H4_4]]]]].
 induction ba.
 inversion H4_1.
 simpl.
 specialize (list_eq_dec (cand_eq_dec) (proj1_sig (fst d)) (proj1_sig (fst a))).
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
Lemma is_first_hopeful_In: forall (c:cand) h l, is_first_hopeful c h l =true -> In c l.
Proof.
 intros c h l H1.
 induction l.
 simpl in H1.
 inversion H1.
 destruct (cand_in_dec a h) as [i1 | i2].
 unfold is_first_hopeful in H1.
 destruct (cand_in_dec c h) as [p1 |p2].
 destruct (cand_eq_dec a c) as [j1 |j2].
 left;assumption.
 destruct (cand_in_dec a h) as [s1 |s2].
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
 destruct (cand_in_dec) as [CandInDec1 | CandInDec2].
 destruct (cand_eq_dec a c) as [CandEqDec1 |CandEqDec2].
 rewrite  CandEqDec1 in i2.
 contradiction i2.
 destruct (cand_in_dec a h) as [CandInDec3 | CandInDec4].
 contradiction i2.
 inversion H1.
 inversion H1.
 simpl.
 destruct (cand_in_dec c h) as [p1 |p2].
 destruct (cand_eq_dec a c ) as [p3 |p4].
 rewrite p3 in i2.
 contradiction i2.
 destruct (cand_in_dec a h) as [p5 |p6].
 contradiction i2.
 destruct (cand_eq_dec a0 c) as [p7 |p8].
 reflexivity.
 destruct (cand_in_dec a0 h) as [p9 |p10].
 reflexivity.
 reflexivity.
 reflexivity.
 rewrite <- Hypo.
 assumption.
Qed.

Lemma list_is_first_hopeful_In: forall (ba: list ballot) (b:ballot) (h: {hopeful:list cand | NoDup hopeful}) (c:cand),  In (proj1_sig (fst b)) (map (fun (d:ballot) => (proj1_sig (fst d))) (list_is_first_hopeful c (proj1_sig h) ba)) -> In c (proj1_sig (fst b)). 
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
Lemma ballot_nodup: forall (ba: list ballot) (t : list (cand ->Q)) (p: cand -> list (list ballot)) (bl: list cand) (e: {elected: list cand | length elected <= st}) (h: {hopeful : list cand | NoDup hopeful}) s,s= state (ba, t, p, bl, e, h) -> forall b: ballot, NoDup (proj1_sig (fst b)).
Proof.
 intros ba t p bl e h  s H1 b.
 destruct b as [[b11 [b121 b122]] b2].
 simpl.
  assumption.
Qed.


(*if c is not the first continuing candidate in a ballot then c does not receives it*)
Lemma weakened_list_is_first_notin: forall (t: list (cand -> Q)) (e: {elected:list cand| length elected <= st}) (p: cand -> list (list ballot))(bl :list cand) c (h: {hopeful: list cand | NoDup hopeful}) (n:Q) ba (d:ballot) (d0:cand) l1 l2, proj1_sig (fst d)= l1++[c]++l2 -> In d0 l1 -> In d0 (proj1_sig h) -> ~ In (proj1_sig (fst d)) (map (fun (d' :ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba)).
Proof.
 intros t e p bl c h n ba d d0 l1 l2 H1 H2 H3.
 induction ba.
 simpl.
 intro.
 auto.
 intro H4.
 specialize (list_eq_dec (cand_eq_dec) (proj1_sig (fst (d))) (proj1_sig (fst a))).
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
Lemma listballot_fcc: forall ba (t: list (cand -> Q)) (p: cand -> list (list ballot)) (bl: list cand) (e: {elected: list cand | length elected <= st}) (h: {hopeful: list cand | NoDup hopeful}) (n:Q), (forall c, In c (proj1_sig h) -> forall d: ballot, In (proj1_sig (fst d)) (map (fun (d':ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba)) <-> fcc ba (proj1_sig h) c d).
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
 exists [].
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

Fixpoint remc (c: cand) (l: list cand) :=
 match l with 
    nil => nil
   | cons l0 ls => if (cand_eq_dec c l0) then ls else cons l0 (remc c ls)
 end.

Lemma remc_ok : forall c:cand, forall l:list cand, NoDup l -> In c l -> eqe c (remc c l) l.
Proof.
 intros c l H1 H2.  
 induction l.
 inversion H2.
 assert (H3: {a =c} + {a <> c}) by apply (cand_eq_dec a c).
 destruct H3 as [H4 | H4].
 replace (remc c (a::l)) with l. 
 unfold eqe.
 exists ([]:list cand).
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
 destruct (cand_eq_dec c c).
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
 destruct (cand_eq_dec c a).
 contradict H4.
 symmetry.
 assumption.
 trivial.
Qed.

Lemma remc_contained_in_list: forall (l: list cand) c a, NoDup l -> In a (remc c l) -> In a l.
Proof.
 intros l c a H H1.
 induction l.
 simpl in H1.
 inversion H1.
 destruct (cand_eq_dec c a0) as [p |q].
 rewrite p in H1.
 simpl in H1.
 destruct (cand_eq_dec a0 a0) as [p1 | p2].
 right;assumption.
 contradiction p2;auto.
 assert (Hypo: (remc c (a0::l))= (a0::remc c l)).
 simpl.
 destruct (cand_eq_dec c a0) as [i | j].
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

Lemma remc_nodup : forall (l : list cand) c, NoDup l -> In c l -> NoDup (remc c l).
Proof.
 intros l c H1 H2.
 induction l.
 inversion H2.
 destruct (cand_eq_dec c a) as [i |j].
 rewrite i.
 simpl.
 destruct (cand_eq_dec a a) as [ p |q].
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
 destruct (cand_eq_dec c a).
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
 exists [].
 exists [].
 split.
 auto.
 apply ord_sing.
 destruct IHx.
 apply (ordered_tl A a0 f x).
 auto.
 destruct s as [z H2].
 destruct H2 as [H5 H6].
 assert (Hyp: {(f a0 < f a)%Q} + {(f a <= f a0)%Q}) by apply (Qlt_le_dec (f a0)(f a)).
 destruct Hyp as [Hyp1 | Hyp2].
 destruct x0.
 simpl in H6.
 simpl in H5.
 rewrite H5 in H1.
 exists [].
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
Lemma NoDup_middle: forall (a:cand) m1 m2, ~ In a (m1++m2) -> NoDup (m1++m2) -> NoDup (m1++[a]++m2).
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
Lemma constructing_electable_first: forall (e: {elected:list cand | length elected <= st}) (f: cand -> Q) (h: {hopeful: list cand | NoDup hopeful}) (qu:Q), st > length (proj1_sig e) -> NoDup (proj1_sig h) -> (existsT m, (forall x:cand, In x m -> In x (proj1_sig h) /\ (qu <= f x)%Q) /\ (ordered f m) /\ NoDup m /\ (length m <= st - (length (proj1_sig e))) /\ (forall x, In x (proj1_sig h) /\ (qu <= f x)%Q /\ length m < st - length (proj1_sig e) -> In x m)). 
Proof.
 intros e f h qu H H1. 
 induction (proj1_sig h).
 exists ([]:list cand).
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
 assert (Hyp1: {(f a < qu)%Q} + {(qu <= f a)%Q}) by apply (Qlt_le_dec (f a) qu).
 destruct Hyp1 as [Hyp1_1 | Hyp1_2].
 specialize (IHl H2).
 destruct IHl as [m H3].
 destruct H3 as [H3_1[ H3_2 H3_3 ]].
 destruct (cand_in_dec a m) as [i | j].
 specialize (H3_1 a i).
 destruct H3_1 as [H3_11 H3_12].
 specialize (Qlt_not_le (f a) qu Hyp1_1);intros H3_4.
 contradiction H3_4.
 exists m.
 split.
 intros x H4.
 split.
 destruct (cand_eq_dec a x) as [p | q].
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
 destruct (cand_in_dec a m) as [i | j].
 specialize (H3_1 a i).
 destruct H3_1 as [H3_11 H3_12].
 specialize (NoDup_remove_2 [] l a H1);intros H5.
 contradiction H5.
 destruct H3_3 as [H3_31 [H3_32 H3_4]].
 specialize (le_lt_eq_dec (length m) (st - length (proj1_sig e)) H3_32);intro H3_33.
 destruct H3_33 as [H3_331 | H3_332].
 specialize (extend_ordered_type cand (f: cand -> Q) m H3_2 a);intro H4.
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
 destruct (cand_eq_dec a x) as [p |q].
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
 destruct (cand_eq_dec a x) as [p | q].
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

Definition update_pile (p: cand -> list (list ballot)) (t: list (cand -> Q)) l (q:Q) (c:cand): list (list ballot):=   
 if cand_in_dec c l 
    then  
        map (map (fun (b : ballot) => 
        (fst b, (Qred (snd b * (Qred ((hd nty t)(c)- q)/(hd nty t)(c))))%Q))) (p c)
    else ( p c).

(*removes every element of the list k which exist in the list l*)
Fixpoint Removel (k :list cand) (l :list cand) :list cand:=
 match l with
        [] => []
        |l0::ls => if (cand_in_dec l0 k) then (Removel k ls) else (l0::(Removel k ls))
 end.

(*if a is not in l, then it is already removed from l*)
Lemma Removel_extra_element: forall a, forall k1 k2 l:list cand, ~ In a l -> Removel (k1++[a]++k2) l = Removel (k1++k2) l. 
Proof.
 intros a k1 k2 l H1.
 induction l.
 simpl.
 auto.
 simpl.
 destruct (cand_in_dec a0 (k1++k2)) as [ i | j].
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
 destruct (cand_in_dec a0 (k1++a::k2)).
 auto.
 contradiction n.
 destruct (cand_in_dec a0 (k1++a::k2)).
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
Lemma Removel_segmentation: forall k l1 l2: list cand, Removel k (l1++l2) = (Removel k l1) ++ (Removel k l2).
Proof.
 intros k l1 l2.
 induction l1.
 simpl.
 auto.
 rewrite<- (app_comm_cons l1 l2 a).
 simpl.
 destruct (cand_in_dec a k) as [ i |j].
 assumption.
 rewrite <- (app_comm_cons ).
 rewrite IHl1.
 auto.
Qed.

(*if the orginal list is duplicate-free, so is any remainder list after removal of some elements*)
Lemma Removel_nodup: forall (k l :list cand), NoDup l -> NoDup (Removel k l).
Proof.
 intros k l H1.
 induction k.
 assert (Hyp: Removel [] l = l).
 induction l.
 simpl.
 auto.
 simpl.
 destruct (cand_in_dec a []).
 inversion i.
 rewrite IHl.
 auto.
 inversion H1.
 assumption.
 rewrite Hyp.
 assumption.
 destruct (cand_in_dec a l) as [i | j].
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
 destruct (cand_in_dec a (a::k)).
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
 destruct (cand_in_dec a k) as [ p | q].
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
 destruct (cand_in_dec a []) as [ i | j].
 inversion i.
 rewrite IHk.
 auto.
Qed.

Lemma nodup_permutation: forall (k l :list cand), (forall x, In x k -> In x l) -> NoDup k -> NoDup l -> Leqe (Removel k l) k l.
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
 destruct (cand_in_dec a l) as [ i | j].
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
 destruct (cand_in_dec a (a::k)) as [p |q].
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
 destruct (cand_in_dec a k) as [p | q]. 
 contradiction H4.
 auto.
 rewrite Hyp10 in IHk.
 unfold Leqe.
 unfold Leqe in IHk.
 assert (Hyp7: k++(Removel k l1)++[a]++(Removel k l2) = (k++(Removel k l1))++[a]++(Removel k l2)).
 rewrite (app_assoc k (Removel k l1) ([a]++(Removel k l2))).
 auto.
 rewrite Hyp7 in IHk.
 specialize (Permutation_reorder cand (l1++[a]++l2) (k++Removel k l1) (Removel k l2) a IHk);intro H7.
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

Lemma Permutation_App: forall l l1 l2:list cand, Permutation l (l1++l2) -> Permutation l (l2++l1).
Proof.
 intros l l1 l2 H1.
 induction l1.
 rewrite app_nil_r.
 rewrite app_nil_l in H1.
 auto.
 apply (Permutation_trans H1).
 apply (Permutation_app_comm).
Qed.  

Lemma Filter_segmentation: forall l a, Filter (a::l) = Filter l \/ (Filter (a::l) = a::Filter l).
Proof.
 intros l a.
 simpl.
 destruct (nodup_elem (proj1_sig (fst a)) && (non_empty (proj1_sig (fst a)))).
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

Lemma Filter_Permutation_ballot: forall l:list ballot, exists l1, Permutation (l1++ (Filter l)) l.
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

(* above this line may be added to the base of the framework *)
(* ********************************************************************************************** *)
(* The following excluded lemmas may be proved later *********************************

Lemma List_IsFirst_decompose : forall c h ba acc, (List_IsFirst_Hopeful c h acc ba) = acc \/ 
  (exists l, List_IsFirst_Hopeful c h acc ba = l ++ acc). 

Lemma In_acc_IsIn_List_IsFirst : forall c h acc ba d, In d acc -> In d (List_IsFirst_Hopeful c h acc ba).

Lemma list_is_first_hopeful_Eq_List_IsFirst_Hopeful : 
 forall c h ba, forall b, In b (list_is_first_hopeful c h ba) -> In b (List_IsFirst_Hopeful c h [] ba).
*) 

Definition Union_InitStep (prem :FT_Judgement) (conc :FT_Judgement): Prop :=
 exists ba ba',  
  prem = initial ba /\
  ba' = (Filter ba) /\
  conc = state(ba', [nty], nas, nbdy, emp_elec, all_hopeful).

Lemma UnionInitStep_IsLegitimate : Is_Legitimate_Initial Union_InitStep.
Proof.
 unfold Is_Legitimate_Initial.
 split.  
 intros.
 exists (state (Filter ba, [nty], nas, nbdy, emp_elec, all_hopeful)). 
 split. auto.
 unfold Union_InitStep.
 exists ba.
 exists (Filter ba).
 split. assumption.
 split;auto. 
 intros.
 unfold Union_InitStep in H.
 destruct H as [ba [ba' H1]]. 
 exists ba. exists ba'. exists [nty]. exists nas. exists nbdy. exists emp_elec. exists all_hopeful.
 split;auto.
 intuition.
 intuition.
Qed.

Definition Union_count (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
 exists ba t nt p np bl h e,                (** count the ballots requiring attention **)
  prem = state (ba, t, p, bl, e, h) /\     (* if we are in an intermediate state of the count *) 
  [] <> ba /\                                        (* and there are ballots requiring attention *)
  (forall c, if (cand_in_dec c (proj1_sig h)) then (exists l,                     
    np(c) = p(c) ++ [l] /\                       
    (forall b, In (proj1_sig (fst b)) (map (fun (d:ballot) => (proj1_sig (fst d))) l) <-> 
                                                               fcc ba (proj1_sig h) c b) /\ 
    (nt (c) = SUM (np(c)))) else ((nt c) = (hd nty t) c) /\ (np c) = (p c)) /\                 
  conc = state ([], nt :: t, np, bl, e, h).     

Lemma UnionCount_IsLegitimate : Is_Legitimate_Count Union_count.
Proof.
 unfold Is_Legitimate_Count.
 split. 
 intros.
 exists (state ([], (fun (c:cand) =>  if (cand_in_dec c (proj1_sig h)) then SUM (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (hd nty t) c) :: t, fun (c:cand) => (if (cand_in_dec c (proj1_sig h)) then (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (p c)), bl, e, h)).
 unfold Union_count.
 exists ba.
 exists t.
 exists ((fun (c:cand) =>  if (cand_in_dec c (proj1_sig h)) then SUM (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else ((hd nty t) c))).
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
 intros p c H.  
 unfold Union_count in H.
 destruct H as [ba [t [nt [ p0 [np [bl [h [e H1]]]]]]]].
 exists ba; exists []; exists t. exists nt; exists p0. 
 exists np; exists bl; exists e; exists h. split. intuition. 
 split; intuition.
 specialize (list_nonempty ballot ba). intro Hyp.
 intuition.
 destruct H2 as [b [l Hyp1]].
 rewrite Hyp1.
 simpl. 
 omega.
Qed.

Definition Union_hwin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h,                            
   prem = state (ba, t, p, bl, e, h) /\           
   length (proj1_sig e) + length (proj1_sig h) <= st /\ 
   w = (proj1_sig e) ++ (proj1_sig h) /\                        
   conc = winners (w).

Lemma  UnionHwin_IsLegitimate : Is_Legitimate_Hwin Union_hwin.                           
Proof.
 unfold Is_Legitimate_Hwin.
 split.
 intros.
 unfold Union_hwin.
 exists (winners ((proj1_sig e) ++ (proj1_sig h))).
 exists ((proj1_sig e) ++ (proj1_sig h)).
 exists ba; exists t; exists p; exists bl; exists e; exists h.  
 auto.
 intros.
 unfold Union_hwin in H. 
 destruct H as [w [ba [t [p [bl [e [h H1]]]]]]]. 
 exists w; exists ba; exists t; exists p; exists bl; exists e; exists h. 
 intuition.
Qed.

Definition Union_ewin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h,                    (** elected win **)
   prem = state (ba, t, p, bl, e, h) /\   (* if at any time *)
   length (proj1_sig e) = st /\             (* we have as many elected candidates as seats *) 
   w = (proj1_sig e) /\                        (* and the winners are precisely the electeds *)
   conc = winners (w).                      (* they are declared the winners *)

Lemma UnionEwin_IsLegitimate : Is_Legitimate_Ewin Union_ewin.
Proof.
 unfold Is_Legitimate_Ewin.
 split.
 intros.
 unfold Union_ewin.
 exists (winners (proj1_sig e)). 
 exists (proj1_sig e). exists ba. exists t. exists p. exists bl. exists e. exists h.
 intuition.
 intros.
 unfold Union_ewin in H.
 destruct H as [w [ba [t [p [bl [e [h H1]]]]]]].
 exists w. exists ba. exists t. exists p. exists bl. exists e. exists h. 
 intuition.
 rewrite <- H0.
 assumption.
Qed.

Definition Union_transfer (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
 exists nba t p np bl nbl h e,         (** transfer votes **) 
  prem = state ([], t, p, bl, e, h) /\ 
  (*if eq_dec_nat (length (proj1_sig e)) st then
  exists w, w= (proj1_sig e) /\  
  conc = winners (w) else *)
    (length (proj1_sig e) < st) /\
    (forall c, In c (proj1_sig h) -> ((hd nty t) c < quota)%Q) /\        (* and we can't elect any candidate *)
    exists l c,                          (* and there exists a list l and a candidate c *)
     (bl = c :: l /\                     (* such that c is the head of the backlog *)
     nbl = l /\                          (* and the backlog is updated by removing the head c *)
     nba = flat_map (fun x => x) (p c) /\            (* and the pile of ballots for c is the new list of ballots requiring attention *)
     np(c) = [] /\                                (* and the new pile for c is empty *)
     (forall d, d <> c -> np(d) = p(d))) /\ (* and the piles for every other candidate remain the same *)   
   conc = state (nba, t, np, nbl, e, h).  

Lemma UnionTransfer_IsLegitimate : Is_Legitimate_Transfer Union_transfer.
Proof.
 unfold Is_Legitimate_Transfer.
 split.
 intros.
 unfold Union_transfer.
 destruct H0 as [H01 [H02 H03]].
 specialize (list_nonempty_type cand bl H02). intro Nonempty_bl.
 destruct Nonempty_bl as [c s].  
 destruct s as [bls H3].  
 exists (state (flat_map (fun x => x) (p c), t, fun d => 
                                                        if (cand_eq_dec d c) then [] else p d, 
                                                        bls, e, h)).
 exists (flat_map (fun x => x) (p c)). exists t. exists p. 
 exists (fun d => if (cand_eq_dec d c) then [] else p d). exists bl. exists bls. exists h. exists e. 
 intuition.
 exists bls. exists c.
 intuition.
 destruct (cand_eq_dec c c). reflexivity.
 contradict f. auto.
 destruct (cand_eq_dec d c).
 contradict H0. assumption.
 auto.
 intros.
 unfold Union_transfer in H.
 destruct H as [nba [t [p [np [bl [nbl [h [e H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [l [ c H141]].
 exists nba; exists t; exists p; exists np; exists bl; exists nbl; exists h; exists e.
 intuition.
 subst.
 simpl.
 omega.
Qed.

Definition Union_elim (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists nba t p np e h nh,                    
   prem = state ([], t, p, [], e, h) /\         
   length (proj1_sig e) + length (proj1_sig h) > st /\ 
   (forall c, In c (proj1_sig h) -> (hd nty t(c) < quota)%Q) /\ 
   exists c,                                            
     ((forall d, In d (proj1_sig h) -> (hd nty t(c) <= hd nty t(d)))%Q /\            
     eqe c (proj1_sig nh) (proj1_sig h) /\                                   
     nba = flat_map (fun x => x) (p c) /\                                   
     np(c)=[] /\                                       
     (forall d, d <> c -> np (d) = p (d))) /\                       
   conc = state (nba, t, np, [], e, nh). 

Lemma UnionElim_IsLegitimate : Is_Legitimate_Elim Union_elim.
Proof.
 unfold Is_Legitimate_Elim.
 split.
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
                                                [], e, exist _ (remc min (proj1_sig h)) H'1)). 
 exists (flat_map (fun x => x) (p min)).
 exists t. exists p. exists (fun d => if (cand_eq_dec d min) then [] else (p d)). exists e. exists h. 
 exists (exist _ (remc min (proj1_sig h)) H'1).
 intuition.
 exists min.
 intuition.
 simpl.
 apply (remc_ok min (proj1_sig h) (proj2_sig h) s1).
 destruct (cand_eq_dec min min). reflexivity.
 contradict f. auto.
 destruct (cand_eq_dec d min). contradiction H0. reflexivity.
 intros. 
 unfold Union_elim in H.
 destruct H as [nba [t [p [np [e [h [nh H1]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [weakest H141]. 
 exists nba. exists t. exists p. exists np. exists e. exists h. exists nh.  
 intuition.
 unfold eqe in H.
 destruct H as [l1 [l2 [H' [H'' [H''' H'''']]]]].
 rewrite H'.
 rewrite H''.
 assert (Hyp : length (l1 ++ [weakest] ++ l2) = (length l1 + (length ([weakest] ++ l2)))% nat).
 simpl.
 rewrite (app_length).
 simpl. auto.  
 rewrite Hyp.
 simpl.
 rewrite (app_length).
 omega.
Qed.

Definition Union_elect (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
 exists t p np (bl nbl: list cand) (nh h: {hopeful: list cand | NoDup hopeful})(e ne: {l : list cand | length l <= st }),
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
     nbl = bl ++ l) /\                                 
  conc = state ([], t, np, nbl, ne, nh).      

Lemma UnionElect_IsLegitimate : Is_Legitimate_Elect Union_elect.
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
 exists (state ([], t, fun c => update_pile p t listElected quota c, bl ++ listElected, 
 exist _ ((proj1_sig e) ++ listElected) Assum, exist _ (Removel listElected (proj1_sig h)) NoDupH)).
 exists t. exists p. exists (fun x => update_pile p t listElected quota x).
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
 unfold update_pile.
 destruct (cand_in_dec c0 listElected).
 trivial.
 contradict f. assumption.
 unfold update_pile.
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

Definition Union_quota := 
 (((inject_Z (Z.of_nat (length (Filter bs)))) / (1 + inject_Z (Z.of_nat st)) + 1)%Q). 

Definition UnionSTV := (mkSTV (Union_quota)  
                         (Union_InitStep) (UnionInitStep_IsLegitimate) 
                         (Union_count) (UnionCount_IsLegitimate)
                         (Union_transfer) (UnionTransfer_IsLegitimate)
                          (Union_elect) (UnionElect_IsLegitimate)
                         (Union_elim) (UnionElim_IsLegitimate)
                          (Union_hwin) (UnionHwin_IsLegitimate)
                         (Union_ewin) (UnionEwin_IsLegitimate)).

Check (Termination).

Lemma init_stages_R_initial : ~ FT_final (initial (Filter bs)).
Proof.
 intro.
 unfold FT_final in H.
 destruct H.
 inversion H.
Qed.
 
Definition Union_Termination := Termination (initial (Filter bs)) init_stages_R_initial UnionSTV.

 (* Below is the transfer rule changed so that all backlog is emptied in one go *)
 (* Replacing this Transfer with Union_transfer, gets us close to ACT Legislative Assembly *)

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

Definition ACT_LH_transfer (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
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
Definition LastParcel_transfer (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
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
Definition ManualACT_elect (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
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

End STV_Framework.

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

  (* ****************************************************** *) 
 (* begining of the proof by first destructing on ba, old proof
 destruct ba.
 destruct (le_lt_dec (length (proj1_sig e) + length (proj1_sig h)) st) as [ les1 | les2 ].
 destruct evidence_hwin0 as [HevHwin1 HevHwin2].
 specialize (HevHwin1 (state ([], t, pile, bl, e, h, q)) [] t pile bl e h q).
 intuition.
 destruct H3 as [conc H31].
 exists conc.
 right; right;right;right;right;left. assumption.
 assert (([]<> (proj1_sig h)) -> existsT d, In d (proj1_sig h) /\  (forall d', In d' (proj1_sig h) -> (t d' <= t d)%Q)).
 apply (list_max_cor cand (proj1_sig h) t).
 assert (forall (q:Q), ((forall c, In c (proj1_sig h) -> 
   (t(c) < q)%Q) + (existsT c: cand, In c (proj1_sig h) /\ (t(c) >= q)%Q))).
 induction (proj1_sig h).
 intro q0.
 left;intros.
 contradict H0.
 assert (forall a: cand, forall h : list cand, [] <> a::h).
 intros.
 intro.
 inversion H0.
 specialize (X (H0 a l)).
 destruct X.
 destruct a0.
 assert (forall (q1: Q), ({(t x < q1)%Q} + {(q1 <= t x)%Q})). intro q1. apply (Qlt_le_dec (t x) q1).
 intro q2.
 specialize (H3 q2).
 destruct H3.
 left.
 intros.
 specialize (H2 c H3).
 apply (Qle_lt_trans (t c) (t x) q2).
 auto. auto.
 right.
 exists x.
 split;auto;auto.
 specialize (X0 q).
 destruct X0.
 destruct bl.
 assert ((proj1_sig h) <> []).
 specialize (list_min cand (proj1_sig h) t).
 intro.
 destruct X0.
 destruct (proj1_sig h).
 rewrite <- app_length in les2.
 rewrite app_nil_r in les2.
 specialize (proj2_sig e).
 intro.
 apply le_lt_or_eq in H0.
 intuition.
 inversion e0.
 destruct s.
 destruct a.
 intro.
 rewrite H2 in H0.
 inversion H0.
 destruct X.
 intro. rewrite <- H1 in H0. apply H0. reflexivity.
 destruct a.
 specialize (list_min cand (proj1_sig h) t).
 intro.
 destruct X.
 rewrite e0 in H0.
 contradict H0. auto.
 destruct s.
 destruct a.
(* case for elimination *)
 destruct evidence_elim0 as [HevElim1 HevElim2].
 specialize (HevElim1 (state ([], t, pile, [], e, h, q)) t pile e h q).
 intuition.
 destruct H8 as [conc Hconc].
 exists conc.
 right;right;right;right;left. auto.
(*end of elim *)
(* the case of ewin or transfer *)
 specialize (lt_eq_lt_dec (length (proj1_sig e)) st); intro LenElected.
 destruct LenElected as [LesEqThanSt | BigThanSt].
 destruct LesEqThanSt as [LesThanSt | EqSt]. 
  (*the case of transfer applies *) 
 destruct evidence_transfer0 as [Hevtrans1 Hevtrans2].
 specialize (Hevtrans1 (state ([], t, pile, c::bl, e, h, q)) t pile (c::bl) e h q).
 intuition.
 assert (Hyp: c:: bl = [] -> False). intro Hyp1. inversion Hyp1. 
 intuition.
 destruct H3 as [conc H31].
 exists conc. 
 right;right;right;left.
 assumption.
 (*the case for ewin*)
 destruct evidence_ewin0 as [HevEwin1 HevEwin2].
 specialize (HevEwin1 (state ([], t, pile, c:: bl, e, h, q)) [] t pile (c:: bl) e h q).
 intuition.
 destruct H3 as [conc H31].
 exists conc.
 right;right;right;right;right;right. 
 auto.  
 destruct e as [e1 e2].
 simpl in BigThanSt.
 omega.
 destruct evidence_elect0 as [HevElect1 HevElect2].
 specialize (HevElect1 (state ([], t, pile, bl, e, h, q)) t pile bl e h q (eq_refl)). 
 specialize (lt_eq_lt_dec (length (proj1_sig e)) st); intro LenElected.
 destruct LenElected as [LenE1 | LenE2]. 
 destruct LenE1 as [LenE11 | LenE12].
 assert (HypE: length (proj1_sig e) + 1 <= st) by omega.
 (*case for elect *)
 destruct s as [c s1].
 assert (HypE2: exists c, (length (proj1_sig e)) + 1 <= st /\ (In c (proj1_sig h)) /\ (q <= t c)%Q). 
 exists c.
 split;auto.
 specialize (HevElect1 HypE2).
 destruct HevElect1 as [conc HevElect21]. 
 exists conc.
 right;right;left. assumption.
 (* the case where someone is over the quota but we have filled all of the vacancies already *)
 destruct evidence_ewin0 as [HevEwin1 HevEwin2]. 
 specialize (HevEwin1 (state ([], t, pile, bl, e, h, q)) [] t pile bl e h q (eq_refl) LenE12).
 destruct HevEwin1 as [conc HevEwin11]. 
 exists conc.
 right; right; right;right;right; right.
 assumption.
 (* the impossible case where e is of length bigger than st *)
 destruct e as [e1 e2]. 
 simpl in LenE2. 
 omega.
 (* the case for count *)
 (* note that I am not specifying not to count if we already have filled the vacancies *)
 destruct evidence_count0 as [HevCount1 HevCount2]. 
 specialize (HevCount1 (state (b ::ba, t, pile, bl, e, h, q)) (b::ba) t pile bl h e q (eq_refl)).
 assert (HyCount: (b:: ba) <> []). intro. inversion H0.
 specialize (HevCount1 HyCount). 
 destruct HevCount1 as [conc HevCount].
 exists conc.
 right;left.
 auto.
 simpl.
 contradict H. unfold FT_final. exists l. reflexivity.
(end of proof by first destructing on ba 
Qed. *)

(* the old formalization ***********************************************)
(*
(* generic notion of a judgement *)
Variable Judgement : Type.
Variable final: Judgement -> Prop.
Hypothesis final_dec: forall j : Judgement, (final j) + (not (final j)).

(* generic well-founded relation on a type *)
Variable WFO : Type.
Variable wfo: WFO -> WFO -> Prop.
Hypothesis wfo_wf: well_founded wfo.

(* the `measure' function *)
Variable m: { j: Judgement | not (final j) } -> WFO.

(* 'make non-final judgement' - pairs a judgement with evidence that it is non-final *)
Definition mk_nfj: forall j: Judgement, forall e: not (final j), { j : Judgement | not (final j) }.
  intros j e. exists j. assumption.
Defined.

(* generic rule - a relation on two judgements *)
Definition Rule := Judgement -> Judgement -> Prop.

(* property 1: the measure always decreases  *)
Definition dec (Rules : list Rule) : Type :=
 forall r, In r Rules -> 
 forall p c : Judgement, r p c ->
 forall ep : not (final p),
 forall ec : not (final c),
 wfo (m (mk_nfj c ec )) (m (mk_nfj p ep)).

(* property 2: for every non-final judgement, there is a rule which may be applied *)
Definition app (Rules : list Rule) : Type := 
 forall p : Judgement, not (final  p) ->
 existsT r, existsT c, (In r Rules * r p c).

(* the type of proofs *)
Inductive Pf (a : Judgement) (Rules : list Rule) : Judgement -> Type := 
 ax : forall j : Judgement, j = a -> Pf a Rules j
 | mkp: forall c : Judgement, 
 forall r : Rule, In r Rules -> 
 forall b : Judgement, r b c ->
 Pf a Rules b ->
 Pf a Rules c.

(* lemma specifying when and how a proof may be 'extended' *)
Lemma extend: 
 forall Rules : list Rule, 
 dec Rules ->
 app Rules ->
 forall a b : Judgement, 
 forall eb: not (final b),
 Pf a Rules b ->
 existsT c : Judgement, 
  (Pf a Rules c) *
  (forall ec: not (final c), wfo (m (mk_nfj c ec)) (m (mk_nfj b eb))).
Proof.
 intros Rules Hdec Happ a b eb Pab.
 unfold dec in Hdec.
 unfold app in Happ. 
 specialize Happ with b.
 destruct Happ as [r Happ]. assumption.
 destruct Happ as [c [Happ1 Happ2]].
 specialize (Hdec r Happ1 b c Happ2). 
 exists c.
 split.
 apply (mkp a Rules c r Happ1 b Happ2 Pab).
 intro ec.
 specialize (Hdec eb ec).
 assumption.
Defined.

(* auxiliary termination theorem *)
Theorem termination_aux : forall Rules : list Rule, 
 dec Rules ->
 app Rules ->
 forall n: WFO,
 forall a b : Judgement, 
 forall eb:  not (final b),
 m (mk_nfj b eb) = n ->
 Pf a Rules b ->  
 (existsT c : Judgement, final c * Pf a Rules c).
Proof.
 intros Rules Hdec Happ n.
 induction n as [w IH] using (well_founded_induction_type wfo_wf).
 intros a b eb Hmb Hab.
 assert (Hex : existsT c : Judgement, 
  (Pf a Rules c) *
  (forall ec: not (final c), wfo (m (mk_nfj c ec)) (m (mk_nfj b eb)))).
 apply (extend Rules Hdec Happ a b eb Hab).
 destruct Hex as [c [Hex1 Hex2]].
 destruct (final_dec c) as [f | nf].
  (* c is final *)
 exists c. split. assumption. assumption.
  (* c is non-final *)
 specialize (Hex2 nf).
 rewrite <- Hmb in IH. 
 destruct (IH (m (mk_nfj c nf)) Hex2 a c nf) as [j Hj].
 reflexivity.
 assumption.
 exists j.
 assumption.
Defined.  

(* the main theorem *)
Corollary termination:  forall Rules : list Rule, 
 dec Rules ->
 app Rules ->
 forall a : Judgement, 
 (existsT c : Judgement, final c * Pf a Rules c).
Proof. 
 intros Rules Hdec Happ a. 
 destruct (final_dec a) as [f | ea].
 exists a. 
 split.
 assumption.
 apply (ax a).
 reflexivity.    
 apply (termination_aux Rules Hdec Happ (m (mk_nfj a ea)) a a ea).
 reflexivity.
 apply (ax a).
 reflexivity.  
Defined. 

End genericTermination.
*)

(*

(* the computational parts of the old formalization *)
(* relation for `first continuing candidate' on a ballot in the list of ballots requiring attention *)
Definition fcc (ba : list ballot) (h : list cand) (c : cand) (b : ballot): Prop := 
  In (proj1_sig (fst b)) ((map (fun (d:ballot) => (proj1_sig (fst d)))) ba) /\
  In c h /\
  (exists l1 l2 : list cand, 
      proj1_sig (fst b) = l1 ++ [c] ++ l2 /\ 
      forall d, (In d l1 -> ~(In d h))).

(* l and nl are equal except that nl additionally contains x *)
Definition eqe {A: Type} (x:A) (l: list A) (nl: list A) : Prop :=
 exists l1 l2: list A, 
  l = l1 ++ l2 /\ 
  nl = l1 ++ [x] ++ l2 /\ 
  (~ In x l1) /\ 
  (~ In x l2).

(* l and nl are equal except that nl additionally contains all the elements of a list k *)

Definition Leqe {A:Type} (k :list A) (l: list A) (nl: list A): Prop:=
 Permutation nl (l++k).

(*updates the pile of candidate c*)
Definition update_pile (p: cand -> list ballot) (t: cand -> Q) (l: list cand) (q:Q) (c:cand): list ballot:=   
 if cand_in_dec c l 
    then  
        map (fun b : ballot => (fst b, (Qred (snd b * (Qred ((t c - q) / t c)))%Q))) (p c)
    else ( p c).

(* empty the pile for one candidate and leave the rest unchanged *)
Definition emp (c: cand) (p: cand -> list ballot) : cand -> list ballot :=
 fun d => if (cand_eq_dec c d) then [] else p d.


(* remove one occurrence of a candidate from a list *)
Fixpoint remc (c: cand) (l: list cand) :=
 match l with 
    nil => nil
   | cons l0 ls => if (cand_eq_dec c l0) then ls else cons l0 (remc c ls)
 end.


(*checks if no cadidate whose name is in h, does not precede the candidate c in the list l*)
Fixpoint is_first_hopeful (c:cand) (h: list cand) (l : list cand):=
 match l with
          [] => false
          |l0::ls =>  if (cand_in_dec c h) then
                                               if cand_eq_dec l0 c then true 
                                               else                     
                                                   if cand_in_dec l0 h then false
                                                   else is_first_hopeful c h ls
                      else false  
 end. 

       

(*collects all of the ballots where c is the first continuing preference*)
Fixpoint list_is_first_hopeful (c:cand) (h: list cand) (ba: list ballot):=
 match ba with
          [] => []
          |b0::bas => if (is_first_hopeful c h (proj1_sig (fst b0))) 
                         then b0::(list_is_first_hopeful c h bas)
                      else (list_is_first_hopeful c h bas)        
 end.


(*removes every element of the list k which exist in the list l*)
Fixpoint Removel (k :list cand) (l :list cand) :list cand:=
 match l with
        [] => []
        |l0::ls => if (cand_in_dec l0 k) then (Removel k ls) else (l0::(Removel k ls))
 end.


Lemma remc_ok : forall c:cand, forall l:list cand, NoDup l -> In c l -> eqe c (remc c l) l.
Proof.
 intros c l H1 H2.  
 induction l.
 inversion H2.
 assert (H3: {a =c} + {a <> c}) by apply (cand_eq_dec a c).
 destruct H3 as [H4 | H4].
 replace (remc c (a::l)) with l. 
 unfold eqe.
 exists ([]:list cand).
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
 destruct (cand_eq_dec c c).
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
 destruct (cand_eq_dec c a).
 contradict H4.
 symmetry.
 assumption.
 trivial.
Qed.

(*if we remove any element from the original list l, every element of the remainder is still a memebr of l*) 
Lemma remc_contained_in_list: forall (l: list cand) c a, NoDup l -> In a (remc c l) -> In a l.
Proof.
 intros l c a H H1.
 induction l.
 simpl in H1.
 inversion H1.
 destruct (cand_eq_dec c a0) as [p |q].
 rewrite p in H1.
 simpl in H1.
 destruct (cand_eq_dec a0 a0) as [p1 | p2].
 right;assumption.
 contradiction p2;auto.
 assert (Hypo: (remc c (a0::l))= (a0::remc c l)).
 simpl.
 destruct (cand_eq_dec c a0) as [i | j].
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

(*if the original list l has no duplicate element and c is removed from it, the remainder list is duplicate free*) 
Lemma remc_nodup : forall (l : list cand) c, NoDup l -> In c l -> NoDup (remc c l).
Proof.
 intros l c H1 H2.
 induction l.
 inversion H2.
 destruct (cand_eq_dec c a) as [i |j].
 rewrite i.
 simpl.
 destruct (cand_eq_dec a a) as [ p |q].
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
 destruct (cand_eq_dec c a).
 contradiction j;auto.
 reflexivity.
Qed.


Lemma Removel_empty: forall k, Removel [] k = k.
Proof.
 intros k.
 induction k.
 simpl.
 auto.
 simpl.
 destruct (cand_in_dec a []) as [ i | j].
 inversion i.
 rewrite IHk.
 auto.
Qed.

(*if x is in the list k, when we remove every elem of k from l, x wont be in the remainder list*)
Lemma Removel_hd: forall x, forall k l, In x k -> ~ In x (Removel k l).
Proof.
 intros x k l H1.
 induction l.
 intro H2.
 simpl in H2.
 auto.
 assert (Hyp: Removel k (a::l) = Removel k l \/ Removel k (a::l) = a:: Removel k l).
 simpl.
 destruct (cand_in_dec a k) as [H |H].
 left.
 auto.
 right.
 auto.
 destruct Hyp as [Hyp1 | Hyp2].
 rewrite Hyp1.
 assumption.
 rewrite Hyp2.
 intro H2.
 destruct H2 as [H3 |H4].
 rewrite <-H3 in H1.
 assert (Hyp3: Removel k (a::l) = Removel k l).
 simpl.
 destruct (cand_in_dec a k).
 auto.
 contradiction n.
 rewrite Hyp3 in Hyp2.
 rewrite Hyp2 in IHl.
 apply IHl.
 left.
 assumption.
 contradiction H4.
Qed.

(*if a is not in l, then it is already removed from l*)
Lemma Removel_extra_element: forall a, forall k1 k2 l:list cand, ~ In a l -> Removel (k1++[a]++k2) l = Removel (k1++k2) l. 
Proof.
 intros a k1 k2 l H1.
 induction l.
 simpl.
 auto.
 simpl.
 destruct (cand_in_dec a0 (k1++k2)) as [ i | j].
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
 destruct (cand_in_dec a0 (k1++a::k2)).
 auto.
 contradiction n.
 destruct (cand_in_dec a0 (k1++a::k2)).
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
Lemma Removel_segmentation: forall k l1 l2: list cand, Removel k (l1++l2) = (Removel k l1) ++ (Removel k l2).
Proof.
 intros k l1 l2.
 induction l1.
 simpl.
 auto.
 rewrite<- (app_comm_cons l1 l2 a).
 simpl.
 destruct (cand_in_dec a k) as [ i |j].
 assumption.
 rewrite <- (app_comm_cons ).
 rewrite IHl1.
 auto.
Qed.

(*if the orginal list is duplicate-free, so is any remainder list after removal of some elements*)
Lemma Removel_nodup: forall (k l :list cand), NoDup l -> NoDup (Removel k l).
Proof.
 intros k l H1.
 induction k.
 assert (Hyp: Removel [] l = l).
 induction l.
 simpl.
 auto.
 simpl.
 destruct (cand_in_dec a []).
 inversion i.
 rewrite IHl.
 auto.
 inversion H1.
 assumption.
 rewrite Hyp.
 assumption.
 destruct (cand_in_dec a l) as [i | j].
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
 destruct (cand_in_dec a (a::k)).
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
 destruct (cand_in_dec a k) as [ p | q].
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

(*for any element a, either a is filtered away or it remains in the list*)
Lemma Filter_segmentation: forall l a, Filter (a::l) = Filter l \/ (Filter (a::l) = a::Filter l).
Proof.
 intros l a.
 simpl.
 destruct (nodup_elem (proj1_sig (fst a)) && (non_empty (proj1_sig (fst a)))).
 right.
 reflexivity.
 left.
 auto.
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

(*the formal and informal ballots put together is a permutation of the total ballots*) 
Lemma Filter_Permutation_ballot: forall l:list ballot, exists l1, Permutation (l1++ (Filter l)) l.
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

Lemma nodup_permutation: forall (k l :list cand), (forall x, In x k -> In x l) -> NoDup k -> NoDup l -> Leqe (Removel k l) k l.
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
 destruct (cand_in_dec a l) as [ i | j].
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
 destruct (cand_in_dec a (a::k)) as [p |q].
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
 destruct (cand_in_dec a k) as [p | q]. 
 contradiction H4.
 auto.
 rewrite Hyp10 in IHk.
 unfold Leqe.
 unfold Leqe in IHk.
 assert (Hyp7: k++(Removel k l1)++[a]++(Removel k l2) = (k++(Removel k l1))++[a]++(Removel k l2)).
 rewrite (app_assoc k (Removel k l1) ([a]++(Removel k l2))).
 auto.
 rewrite Hyp7 in IHk.
 specialize (Permutation_reorder cand (l1++[a]++l2) (k++Removel k l1) (Removel k l2) a IHk);intro H7.
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
(*lists that are permuattions of one another contain the same elements*)

Lemma Permutation_notin: forall l1 l2, Permutation l1 l2 -> forall x:cand, ~ In x l1 -> ~ In x l2.
Proof.
 intros l1 l2 H1 x H2.
 induction l1.
 specialize (Permutation_nil H1);intro H3.
 rewrite H3;intro.
 inversion H.
 destruct (cand_eq_dec a x).
 rewrite e in H2.
 intro.
 apply H2.
 left;auto.
 intro.
 specialize (Permutation_sym H1);intro H3.
 specialize (Permutation_in x H3).
 intro.
 specialize (H0 H).
 contradiction H2.
Qed.

(*if a list has no duplication, then adding elements which were not in it does not creat duplication.*)
Lemma NoDup_middle: forall (a:cand) m1 m2, ~ In a (m1++m2) -> NoDup (m1++m2) -> NoDup (m1++[a]++m2).
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

Lemma list_nonempty: forall l: list cand, [] = l \/ exists b l', l= b::l'.
Proof.
 intros l.
 induction l.
 left.
 auto.
 destruct IHl as [i | j].
 right.
 exists a.
 exists [].
 rewrite <- i.
 auto.
 destruct j as [b [l' H1]].
 right.
 exists a.
 exists (b::l').
 rewrite H1.
 reflexivity.
Qed.

Lemma nonempty_list_notempty: forall l1 l2 (c:cand), [] <> l1++[c]++l2.
Proof.
 intros l1' l2' c'.   
 intro H'.       
 induction l1'.
 simpl in H'.
 inversion H'.
 rewrite <- (app_comm_cons) in H'.       
 inversion H'.
Qed.
(*we can decide if two given natural numbers are equal*)

Lemma eq_dec_nat : forall n m:nat, {n = m} + {n <> m}.
Proof.
 intros n m.
 specialize (lt_eq_lt_dec n m);intro H1.
 destruct H1 as [H2 | H3].
 destruct H2 as [H21 | H22].
 right.
 intro H4.
 rewrite H4 in H21.
 omega.
 left;assumption.
 right.
 intro H1.
 rewrite H1 in H3.
 omega.
Qed.

(*ordering elements of a list with respect to their value in terms of function f*)
Inductive ordered {A : Type} (f : A -> Q) : list A -> Prop := 
  ord_emp : ordered f []  
 | ord_sing : forall x : A, ordered f [x]
 | ord_cons : forall l x y, ordered f (y :: l) -> (f(x) >= f(y))%Q -> ordered f (x :: y :: l).

(*if a list is ordered w.r.t. function f, then its tail is also ordered w.r.t.*)
Lemma ordered_tl: forall (A:Type)(a:A) f l, ordered f (a::l) -> ordered f l.
Proof.
 intros A a f l H0.
 inversion H0.
 apply ord_emp.
 auto.
Qed.

Lemma ordered_head: forall (A: Type) (x y:A) r f, ordered f (x::y::r) -> (f x >= f y)%Q.
Proof.
 intros.
 inversion H.
 auto.
Qed.

(*if a list is oredered w.r.t. f, then adding to the head an element a which is bigger than all the other elems w.r.t. f, we still get an ordered list w.r.t. f*)
Lemma ordered_related: forall (A:Type) f l, ordered f l -> (forall a:A, (forall b, In b l -> (f b <= f a)%Q) -> ordered f (a::l)).
Proof.
 intros.
 inversion H.
 apply ord_sing.
 rewrite<- H1 in H.
 rewrite H1.
 assert (Hyp: In x l).
 rewrite<-  H1.
 left;auto.
 specialize (H0  x Hyp).
 rewrite <- H1.
 apply ord_cons.
 auto.
 assumption.
 rewrite<- H3 in H.
 apply ord_cons.
 auto.
 rewrite <- H3 in H0.
 apply (H0 x).
 left;auto.
Qed.

(*an ordered list w.r.t. f, is indeed ordered w.r.t. so that order is correct*)
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

Lemma ordered_app: forall (A:Type) f (l':list A), (forall l, ordered f (l++l') -> ordered f l').
Proof.
 intros.
 induction l.
 auto.
 apply IHl.
 rewrite <- app_comm_cons in H.
 apply (ordered_tl A a f (l++l')) in H.
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

(* if a list is ordered w.r.t. function f, given a new element a, one can always insert a into the list without destroying the order.*)
Lemma extend_ordered_type: forall A:Type, forall f: A -> Q, forall x: list A, ordered f x -> (forall a:A, (existsT y z, x =y++z /\ ordered f (y++[a]++z))).
Proof.
 intros A f x H1 a.
 induction x.
 exists [].
 exists [].
 split.
 auto.
 apply ord_sing.
 destruct IHx.
 apply (ordered_tl A a0 f x).
 auto.
 destruct s as [z H2].
 destruct H2 as [H5 H6].
 assert (Hyp: {(f a0 < f a)%Q} + {(f a <= f a0)%Q}) by apply (Qlt_le_dec (f a0)(f a)).
 destruct Hyp as [Hyp1 | Hyp2].
 destruct x0.
 simpl in H6.
 simpl in H5.
 rewrite H5 in H1.
 exists [].
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


Lemma Permutation_app: forall l l1 l2:list cand, Permutation l (l1++l2) -> Permutation l (l2++l1).
Proof.
 intros l l1 l2 H1.
 induction l1.
 rewrite app_nil_r.
 rewrite app_nil_l in H1.
 auto.
 apply (Permutation_trans H1).
 apply (Permutation_app_comm).
Qed.  

Lemma Permutation_nodup: forall l1 l2:list cand, Permutation l1 l2 -> NoDup l1 -> NoDup l2. 
Proof.
 intros l1 l2 H1 H2.
 induction H1.
 assumption.
 apply NoDup_cons.
 inversion H2.
 apply (Permutation_notin l l' H1).
 assumption.
 apply IHPermutation.
 inversion H2.
 assumption.
 inversion H2.
 inversion H3.
 apply NoDup_cons.
 intro.
 destruct H8.
 rewrite H8 in H1.
 apply H1.
 left;auto.
 contradiction H6.
 apply NoDup_cons.
 intro.
 apply H1.
 right;auto.
 assumption.
 apply IHPermutation2.
 apply IHPermutation1.
 assumption.
Qed.

(*if there are vacancies, we can construct a list electable candidates who have reached the quota. Besides this list is orderedw.r.t. tally, and it contains all of such electable candidates.*)
Lemma constructing_electable_first: forall (e: {elected:list cand | length elected <= st}) (f: cand -> Q) (h: {hopeful: list cand | NoDup hopeful}) (qu:Q), st > length (proj1_sig e) -> NoDup (proj1_sig h) -> (existsT m, (forall x:cand, In x m -> In x (proj1_sig h) /\ (qu <= f x)%Q) /\ (ordered f m) /\ NoDup m /\ (length m <= st - (length (proj1_sig e))) /\ (forall x, In x (proj1_sig h) /\ (qu <= f x)%Q /\ length m < st - length (proj1_sig e) -> In x m)). 
Proof.
 intros e f h qu H H1. 
 induction (proj1_sig h).
 exists ([]:list cand).
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
 assert (Hyp1: {(f a < qu)%Q} + {(qu <= f a)%Q}) by apply (Qlt_le_dec (f a) qu).
 destruct Hyp1 as [Hyp1_1 | Hyp1_2].
 specialize (IHl H2).
 destruct IHl as [m H3].
 destruct H3 as [H3_1[ H3_2 H3_3 ]].
 destruct (cand_in_dec a m) as [i | j].
 specialize (H3_1 a i).
 destruct H3_1 as [H3_11 H3_12].
 specialize (Qlt_not_le (f a) qu Hyp1_1);intros H3_4.
 contradiction H3_4.
 exists m.
 split.
 intros x H4.
 split.
 destruct (cand_eq_dec a x) as [p | q].
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
 destruct (cand_in_dec a m) as [i | j].
 specialize (H3_1 a i).
 destruct H3_1 as [H3_11 H3_12].
 specialize (NoDup_remove_2 [] l a H1);intros H5.
 contradiction H5.
 destruct H3_3 as [H3_31 [H3_32 H3_4]].
 specialize (le_lt_eq_dec (length m) (st - length (proj1_sig e)) H3_32);intro H3_33.
 destruct H3_33 as [H3_331 | H3_332].
 specialize (extend_ordered_type cand (f: cand -> Q) m H3_2 a);intro H4.
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
 destruct (cand_eq_dec a x) as [p |q].
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
 destruct (cand_eq_dec a x) as [p | q].
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

(*every ballot b which c is its first preference, is an elements of the uncounted ballots ba, so that ballots are not assigned to a cadidate from an illegal source*) 
Lemma weakened_is_first_hopeful_ballot: forall c h ba, forall (d:ballot), In (proj1_sig (fst d)) (map (fun (d0:ballot) => (proj1_sig (fst (d0)))) (list_is_first_hopeful c h ba)) -> In (proj1_sig (fst d)) (map (fun (d: ballot) => (proj1_sig (fst d))) ba).
Proof.
 intros.
 induction ba.
 simpl in H.
 inversion H.
 specialize (list_eq_dec (cand_eq_dec) (proj1_sig (fst d)) (proj1_sig (fst a))).
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

(*if c is not the first continuing candidate in a ballot, then he does not receive that vote*) 
Lemma first_hopeful_false: forall c h d0 l1 l2, In d0 l1 -> In d0 h -> NoDup (l1++[c]++l2) -> is_first_hopeful c h (l1++[c]++l2) = false.
Proof.
 intros c h d0 l1 l2 H1 H2 H3.
 induction l1.
 simpl.
 inversion H1.
 destruct (cand_eq_dec d0 a).
 simpl.
 destruct (cand_in_dec c h) as [CandInDec1 |CandInDec2].
 destruct (cand_eq_dec a c) as [i | j].
 rewrite i in H3.
 inversion H3.
 assert (Hypo: In c (l1++c::l2)).
 intuition.
 contradiction H4.
 destruct (cand_in_dec a h) as [p |q].
 auto.
 rewrite e in H2.
 contradiction q.  auto.
 simpl.
 destruct (cand_in_dec c h) as [CandInDec1 | CandInDec2].
 destruct (cand_eq_dec a c) as [i' | j'].
 rewrite i' in H3.
 inversion H3.
 exfalso.
 apply H4.
 intuition.
 destruct (cand_in_dec a h) as [p' |q'].
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
Lemma first_hopeful_true: forall c (h: {hopeful: list cand | NoDup hopeful}) (b:ballot) (ba: list ballot) l1 l2,(forall d, In d l1 -> ~ In d (proj1_sig h)) /\ (exists (d:ballot), (proj1_sig (fst d)) = l1++[c]++l2) /\ (In c (proj1_sig h)) -> is_first_hopeful c (proj1_sig h) (l1++[c]++l2) = true.
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
 destruct (cand_in_dec c (proj1_sig h)) as [CandInDec1 | CandInDec2].
 destruct (cand_eq_dec c c) as [i1 |i2].
 auto.
 contradiction i2.
 auto.
 contradiction CandInDec2.
 simpl.
 destruct (cand_in_dec c (proj1_sig h) ) as [CandInDec3 | CandInDec4].
 destruct (cand_in_dec a (proj1_sig h)).
 specialize (H11 a).
 assert (Hypo: In a (a::l1)).
 left;auto.
 specialize (H11 Hypo).
 contradiction H11.
 destruct (cand_eq_dec a c) as [CandEqDec1 |CandEqDec2].
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
 exists ((exist _ (l1++[c]++l2) Hypo4), (1)%Q).
 simpl.
 auto.
 inversion Hypo1.
 simpl;assumption.
 specialize (nonempty_list_notempty l1 l2 c);intro Hypo6;auto.            
 contradiction CandInDec4.
Qed.

(*c receives all of the ballots that prefer him as their first contiuing choice*)
Lemma fcc_listballot: forall ba (h: {hopeful: list cand | NoDup hopeful}),(forall c, forall d: ballot,  fcc ba (proj1_sig h) c d -> In (proj1_sig (fst d)) (map (fun (d0:ballot) => (proj1_sig (fst d0))) (list_is_first_hopeful c (proj1_sig h) ba))).
Proof.
 intros ba h c.
 intros d H4.
 unfold fcc in H4.
 destruct H4 as [H4_1 [H4_2 [l1 [l2 [H4_3 H4_4]]]]].
 induction ba.
 inversion H4_1.
 simpl.
 specialize (list_eq_dec (cand_eq_dec) (proj1_sig (fst d)) (proj1_sig (fst a))).
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
Lemma is_first_hopeful_In: forall (c:cand) h l, is_first_hopeful c h l =true -> In c l.
Proof.
 intros c h l H1.
 induction l.
 simpl in H1.
 inversion H1.
 destruct (cand_in_dec a h) as [i1 | i2].
 unfold is_first_hopeful in H1.
 destruct (cand_in_dec c h) as [p1 |p2].
 destruct (cand_eq_dec a c) as [j1 |j2].
 left;assumption.
 destruct (cand_in_dec a h) as [s1 |s2].
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
 destruct (cand_in_dec) as [CandInDec1 | CandInDec2].
 destruct (cand_eq_dec a c) as [CandEqDec1 |CandEqDec2].
 rewrite  CandEqDec1 in i2.
 contradiction i2.
 destruct (cand_in_dec a h) as [CandInDec3 | CandInDec4].
 contradiction i2.
 inversion H1.
 inversion H1.
 simpl.
 destruct (cand_in_dec c h) as [p1 |p2].
 destruct (cand_eq_dec a c ) as [p3 |p4].
 rewrite p3 in i2.
 contradiction i2.
 destruct (cand_in_dec a h) as [p5 |p6].
 contradiction i2.
 destruct (cand_eq_dec a0 c) as [p7 |p8].
 reflexivity.
 destruct (cand_in_dec a0 h) as [p9 |p10].
 reflexivity.
 reflexivity.
 reflexivity.
 rewrite <- Hypo.
 assumption.
Qed.

Lemma list_is_first_hopeful_In: forall (ba: list ballot) (b:ballot) (h: {hopeful:list cand | NoDup hopeful}) (c:cand),  In (proj1_sig (fst b)) (map (fun (d:ballot) => (proj1_sig (fst d))) (list_is_first_hopeful c (proj1_sig h) ba)) -> In c (proj1_sig (fst b)). 
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
*)




(*

Definition initial_step (prem :FT_Judgement) (conc :FT_Judgement): Prop :=
 exists ba ba' qu,  
  prem = initial ba /\
  ba' = (Filter ba) /\
  ((qu= (((inject_Z (Z.of_nat (length ba'))) / (1 + inject_Z (Z.of_nat st)) + 1)%Q) ) /\ exists l, Permutation (l ++ ba') ba ) /\
  conc = state(ba', nty, nas, nbdy, emp_elec, all_hopeful,qu ).

Definition count (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
 exists ba t nt p np bl h e qu,                (** count the ballots requiring attention **)
  prem = state (ba, t, p, bl, e, h,qu) /\     (* if we are in an intermediate state of the count *) 
  [] <> ba /\                                        (* and there are ballots requiring attention *)
  (forall c, if (cand_in_dec c (proj1_sig h)) then (exists l,                              (* and for each candidate c there is a list of ballots *)
    np(c) = p(c) ++ l /\                       (* such that the pile for c is updated by adding these ballots to the top *)
    (forall b, In (proj1_sig (fst b)) (map (fun (d:ballot) => (proj1_sig (fst d))) l) <-> fcc ba (proj1_sig h) c b) /\ (* and a ballot is added to c's pile iff c is the first continuing candidate on the ballot *)
    nt(c) = sum (np(c))) else (nt c) = (t c) /\ (np c) = (p c)) /\                  (* and the new tally for c is the sum of the weights of the ballots in c's pile *)
  conc = state ([], nt, np, bl, e, h,qu).     (* then we proceed with no ballots requiring attention and updated piles and tallies *) 

Definition transfer (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
 exists nba t p np bl nbl h e qu,         (** transfer votes **) 
  prem = state ([], t, p, bl, e, h,qu) /\ 
  if eq_dec_nat (length (proj1_sig e)) st then
  exists w, w= (proj1_sig e) /\  
  conc = winners (w) else
    ( 
    (forall c, In c (proj1_sig h) -> (t(c) < qu)%Q) /\        (* and we can't elect any candidate *)
    exists l c,                                    (* and there exists a list l and a candidate c *)
     (bl = c :: l /\                               (* such that c is the head of the backlog *)
     nbl = l /\                                    (* and the backlog is updated by removing the head c *)
     nba = p(c) /\                                 (* and the pile of ballots for c is the new list of ballots requiring attention *)
     np(c) = [] /\                                (* and the new pile for c is empty *)
     (forall d, d <> c -> np(d) = p(d))) /\ (* and the piles for every other candidate remain the same *)   conc = state (nba, t, np, nbl, e, h, qu)).  (* then continue with the new pile of ballots requiring attention and updated piles and backlog *)


Definition elect (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
 exists (ba: list ballot) (t: cand -> Q) (p np: cand -> list ballot) (bl nbl: list cand) (nh h: {hopeful: list cand | NoDup hopeful})(e ne: {l : list cand | length l <= st }) qu,
    let (els, elp) := e in                (*  e and ne are sigma-types: {l : list cand | length l <= s } *)
    let (nels, nelp) := ne in
    prem = state ([], t, p, bl, e, h, qu) /\ (* if there are no ballots requiring attentions *)
    exists l,                                      (* and there is a list l *)
     (l <> [] /\                                   (* that is non empty *)
     length l <= st - length (proj1_sig e) /\   (* and is no greater than the number of available seats *) 
     (forall c, In c l -> In c (proj1_sig h) /\ (t(c) >= qu)%Q) /\       (* and contains the candidates who have reached the quota*)
     ordered t l /\ (* and l is ordered by tally, with the greatest at the head of the list *)
     Leqe l (proj1_sig nh) (proj1_sig h) /\           (* and all of the candidates over quota have been removed from the hopefuls *)
     Leqe l els nels /\      (* and added to the list of elected candidates *)
     (forall c, In c l -> (np c = map (fun (b : ballot) => 
        (fst b, (Qred (snd b * (Qred ((t(c)-qu)/t(c))))%Q))) (p c))) /\   (* and the piles for the candidates over quota are updated by transfer balue *)
     (forall c, ~ In c l -> np (c) = p (c)) /\  (* and the piles for all other candidates remain the same *)
     nbl = bl ++ l) /\                                  (* and the backlog is updated by adding l to the end *)
  conc = state ([], t, np, nbl, ne, nh, qu).      (* then continue counting with updated piles, backlog, electeds and hopefuls *)


Definition elim (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists nba t p np e h nh qu,                    (** eliminate a hopeful **)
   prem = state ([], t, p, [], e, h, qu) /\          (* if there are no ballots requiring attention and no backlog*)
   length (proj1_sig e) + length (proj1_sig h) > st /\ (* and the sum of the elected candidates and hopfuls is greater than the number of seats *)
   (forall c, In c (proj1_sig h) -> (t(c) < qu)%Q) /\    (* and all of the hopefuls are under the quota *)
   exists c,                                             (* and there is a candidate c *)
     ((forall d, In d (proj1_sig h) -> (t(c) <= t(d)))%Q /\            (* with minimum tally *)
     eqe c (proj1_sig nh) (proj1_sig h) /\                                   (* and the hopefuls are updated by removing c *)
     nba = p(c) /\                                    (* and the new list of ballots to requiring attention is c's pile *)
     np(c)=[] /\                                        (* and the new pile for c is empty *)
     (forall d, d <> c -> np (d) = p (d))) /\  (* and every other pile remains the same *)                                         
   conc = state (nba, t, np, [], e, nh, qu).  (* then continute counting with updated ballots requiring attentions, piles and hopefuls *)

Definition hwin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h qu,                            (** hopefuls win **)
   prem = state (ba, t, p, bl, e, h, qu) /\           (* if at any time *)
   length (proj1_sig e) + length (proj1_sig h) <= st /\ (* we have fewer hopefuls and electeds  than seats *)
   w = (proj1_sig e) ++ (proj1_sig h) /\                        (* and the winning candidates are their union *)
   conc = winners (w).                              (* the elected cands and the remaining hopefuls are declared winners *)

Definition ewin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h qu,                    (** elected win **)
   prem = state (ba, t, p, bl, e, h, qu) /\   (* if at any time *)
   length (proj1_sig e) = st /\             (* we have as many elected candidates as setas *) 
   w = (proj1_sig e) /\                        (* and the winners are precisely the electeds *)
   conc = winners (w).                      (* they are declared the winners *)

Definition FTR : list FT_Rule := [initial_step;count; transfer; elect; elim; hwin; ewin].

*)

(*
(* proof of dec property *)
(* proof done rule by rule *)
(* initial_step decreases the measure of complexity *)
Lemma dec_FT_initial : forall p c : FT_Judgement,
initial_step p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof.
 intros p c Hr ep ec.
 destruct p.
 destruct c.  
 inversion Hr.
 destruct H as [ba' [qu [H0 [H1 [H2 H3]]]]].
 inversion H3.
      (*case for initial-state*)
 destruct p as [[[[[[ba2 t2] p2] bl2] e2] h2] qu].
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite wfo_aux. 
 left;auto. 
      (*case for initial-final*)
 destruct ec. 
 inversion Hr.
 destruct H as [ba' [qu [H0 [H1 [H2 H3]]]]].
 inversion H3.
      (*case for step*)
 destruct c;
 repeat
  (destruct Hr;destruct H as [ba' [qu [H0 [H1 [H2 H3]]]]];inversion H3)
   ||
    (destruct Hr;destruct H as [ba' [qu [H0 [H1 [H2 H3]]]]]) 
    || inversion H0.
 destruct ep.
 exists l.
 reflexivity.
Qed.
    
(*count decreases the measure of complexity*)
Lemma dec_FT_count : forall p c : FT_Judgement,
count p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
 intros p c Hr ep ec.
 destruct p. 
 destruct c.
   (* non final judgements *)
 destruct Hr. destruct H as [t [nt [p' [np [bl [h [e [qu H1]]]]]]]]. destruct H1 as [H11 H12]. inversion H11.
 destruct Hr. destruct H as [t [nt [p' [np [bl [h [e [qu H1]]]]]]]]. destruct H1 as [H11 H12]. inversion H11.
 destruct Hr. destruct H as [t [nt [p' [np [bl [h [e [qu H1]]]]]]]]. destruct H1 as [H11 H12]. inversion H11.
 destruct c.
 destruct Hr.
 destruct H as [t [nt [p' [np [bl [h [e [qu H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14 ]]]. inversion H14.
 destruct p as [[[[[[ba1 t1] p1] bl1] e1] h1] q1].
 destruct p0 as [[[[[[ba2 t2] p2] bl2] e2] h2] q2].
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 right. right. right.
 unfold count in Hr.
 destruct Hr as [ba [t [nt [p [np [bl [h [e [qu H]]]]]]]]].
 destruct H as [Heq1 [Hba [Hc Heq2]]].
 inversion Heq1.  
 inversion Heq2. subst.
 split. reflexivity. 
 split. reflexivity.
 split. reflexivity.
 simpl.
 destruct ba. 
 contradict Hba. reflexivity. 
 simpl. intuition.
  (* final jugements *)
 unfold FT_final in ec.
 contradict ec.
 exists l. reflexivity.
 unfold FT_final in ep.
 contradict ep.
 exists l. reflexivity.
Qed. 

(*transfer decreases the measure of complexity*)
Lemma dec_FT_transfer : forall p c : FT_Judgement,
transfer p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
 intros p c Hr ep ec.
 destruct p.
   (*case of initial*)
 repeat destruct c; destruct Hr; destruct H as [t [p1 [np [bl [nbl [h [e [qu H1]]]]]]]]; destruct H1 as [H11 H12]; inversion H11.
 destruct c. 
 destruct Hr.  
 destruct H as [t [p1 [np [bl [nbl [h [e [qu H1]]]]]]]].
 destruct H1 as [H11 H12].
 destruct eq_dec_nat.  
 destruct H12 as [w [H121 H122]]. inversion H122.
 destruct H12 as [H12_1 [H12_2 [H12_3 [H12_4 H12_5]]]]. inversion H12_5.  
 destruct p as [[[[[[ba1 t1] p1] bl1] e1] h1] q1].  
 destruct p0 as [[[[[[ba2 t2] p2] bl2] e2] h2] q2].
   (* non final judgements *)
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 right. right. left. 
 unfold transfer in Hr.
 destruct Hr as [nba [t [p [np [bl [nbl [h [e [qu H]]]]]]]]].
 destruct H as [Heq1 Hinh1].
 destruct (eq_dec_nat).  
 destruct Hinh1.    
 destruct H.
 inversion H0.
 destruct Hinh1 as [Hinh2 Hinh].
 destruct Hinh as [l [c [Hex Heq2]]].      
 inversion Heq1.  
 inversion Heq2. subst.
 split. reflexivity.
 split. reflexivity.
 destruct Hex as [Hex1 [Hex2 Hex]].
 rewrite -> Hex1, Hex2.
 intuition.   
  (* final jugements *)
 unfold FT_final in ec.
 contradict ec.
 exists l. reflexivity.
 unfold FT_final in ep.
 contradict ep.
 exists l. reflexivity.
Qed. 

Lemma dec_FT_elect : forall p c : FT_Judgement,
elect p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
 intros p c Hr ep ec.
 destruct p.
 destruct c.
 unfold elect in Hr;destruct Hr as [ba [t [p' [np [bl [nbl [h [nh [e [ne [qu H]]]]]]]]]]];destruct e;destruct ne;destruct H as [H1 H2]; inversion H1.
 unfold elect in Hr;destruct Hr as [ba [t [p' [np [bl [nbl [h [nh [e [ne [qu H]]]]]]]]]]];destruct e;destruct ne;destruct H as [H1 H2]; inversion H1.
 unfold elect in Hr;destruct Hr as [ba [t [p' [np [bl [nbl [h [nh [e [ne [qu H]]]]]]]]]]];destruct e;destruct ne;destruct H as [H1 H2]; inversion H1. 
 destruct c.
 unfold elect in Hr;destruct Hr as [ba [t [p' [np [bl [nbl [h [nh [e [ne [qu H]]]]]]]]]]];destruct e;destruct ne. destruct H as [H1 [H2 [H3 H4]]];inversion H4.
 destruct p as [[[[[[ba1 t1] p1] bl1] e1] h1] q1].  
 destruct p0 as [[[[[[ba2 t2] p2] bl2] e2] h2] q2].
   (* non final judgements *) 
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 right. left. 
 unfold elect in Hr.
 destruct Hr as [ba [t [p [np [bl [nbl [h [nh [e [ne [qu H]]]]]]]]]]].
 destruct e.
 destruct ne.
 destruct H as [Heq1 [k [Hc Heq2]]].
 inversion Heq1.  
 inversion Heq2. subst.
 destruct Hc as [H1 [H2 [H3 [H4 [H5 H6]]]]].
 destruct k.
 contradict H1. reflexivity.
 unfold Leqe in H5.
 specialize (Permutation_length  H5);intro H51.
 rewrite H51.
 rewrite (app_length).
 simpl.
 omega.
  (* final jugements *)
 unfold FT_final in ec.
 contradict ec.
 exists l.  
 reflexivity.
 unfold FT_final in ep.
 contradict ep.
 exists l. reflexivity.
Qed.

Lemma dec_FT_elim : forall p c : FT_Judgement,
elim p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
 intros p c Hr ep ec.
 destruct p.
 unfold elim in Hr.  
 destruct Hr as [nba [t [p0 [np [e [h [nh [qu H1]]]]]]]].     
 destruct H1 as [H11 H12]. inversion H11.
 destruct c.
 destruct Hr as [nba [t [p' [np [e [h [nh [qu H1]]]]]]]].   
 destruct H1 as [H11 [H12 [H13 [H14 [H15 H16]]]]]. inversion H16.
 destruct p as [[[[[[ba1 t1] p1] bl1] e1] h1] q1].  
 destruct p0 as [[[[[[ba2 t2] p2] bl2] e2] h2] q2].
   (* non final judgements *)
 unfold FT_m.
 simpl.
 unfold FT_wfo.
 rewrite -> wfo_aux.
 right. left. 
 unfold elim in Hr.
 destruct Hr as [nba [t [p [np [e [h [nh [qu H]]]]]]]].   
 destruct H as [Heq1 [Hl [Hc [c [Ht Heq2]]]]].
 inversion Heq1. 
 inversion Heq2. 
 subst. 
 destruct Ht as [H1 [H2 H3]]. 
 unfold eqe in H2.
 destruct H2 as [l1 [l2 [h1 h2]]].
 rewrite h1.
 destruct h2 as [h21 [h22 h23]].
 rewrite h21.
 simpl.
 rewrite app_length.
 rewrite (app_length l1 (c::l2)).
 simpl.
 split. reflexivity.
 omega.
  (* final jugements *)
 unfold FT_final in ec.
 contradict ec.
 exists l. reflexivity.
 unfold FT_final in ep.
 contradict ep.
 exists l. reflexivity.
Qed.

Lemma dec_FT_hwin : forall p c : FT_Judgement,
hwin p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof.
 intros p c Hr ep ec.
 destruct p.   
 repeat destruct c;
 unfold hwin in Hr;
 destruct Hr as [w [ba [t [p' [bl [e [h [qu [n H1]]]]]]]]]; inversion n. 
 destruct c.
 unfold hwin in Hr; destruct Hr as [w [ba [t [p' [bl [e [h [qu [n H1]]]]]]]]]; destruct H1 as [H11 [H12 H14]];inversion H14.
 destruct p as [[[[[[ba1 t1] p1] bl1] e1] h1] q1].
 destruct p0 as [[[[[[ba2 t2] p2] bl2] e2] h2] q2].
 unfold hwin in Hr. 
 destruct Hr as [w [ba [t [p [bl [e [h [qu [n H]]]]]]]]].
 destruct H as [Heq1 [Hl Heq2]].
 inversion Heq2.
 unfold FT_final in ec.
 contradict ec.
 exists l. reflexivity.   
  (* final jugements *)
 unfold FT_final in ep.
 contradict ep.
 exists l. reflexivity.
Qed.

Lemma dec_FT_ewin : forall p c : FT_Judgement,
ewin p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof.
 intros p c Hr ep ec.
 destruct p. 
 unfold ewin in Hr.
 destruct Hr as [w [ba [t [p' [bl [e [h [qu [H1 H2]]]]]]]]].
 inversion H1.
 destruct c.
 destruct Hr as [w' [ba' [t' [p' [bl [e [h [qu H1]]]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 inversion H14.
 destruct p as [[[[[[ba1 t1] p1] bl1] e1] h1] q1].  
 destruct p0 as [[[[[[ba2 t2] p2] bl2] e2] h2] q2].
 unfold ewin in Hr. 
 destruct Hr as [w [ba [t [p [bl [e [h [qu H]]]]]]]].
 destruct H as [Heq1 [Hl [Hw Heq2]]].
 inversion Heq2.
 unfold FT_final in ec.
 contradict ec.
 exists l. reflexivity.   
  (* final jugements *)
 unfold FT_final in ep.
 contradict ep.
 exists l. reflexivity.
Qed.

(*all of the rules decrease the complexity measure*)
Lemma dec_FT : dec FT_Judgement FT_final FT_WFO FT_wfo FT_m FTR. 
Proof. 
 unfold dec.
 intros r Hin p c Hr ep ec.
 destruct Hin.
 rewrite <- H in Hr.
 apply dec_FT_initial.
 assumption.
 destruct H.
 rewrite <- H in Hr.
 apply dec_FT_count. 
 assumption.
 destruct H.
 rewrite <- H in Hr.
 apply dec_FT_transfer. 
 assumption.     
 destruct H.
 rewrite <- H in Hr.
 apply dec_FT_elect. 
 assumption.
 destruct H.
 rewrite <- H in Hr.
 apply dec_FT_elim. 
 assumption.
 destruct H.
 rewrite <- H in Hr.
 apply dec_FT_hwin. 
 assumption.
 destruct H.
 rewrite <- H in Hr.
 apply dec_FT_ewin. 
 assumption.
 destruct H.
Qed.                      


(*all the ballots which have already been filtered have no duplicate*)
Lemma ballot_nodup: forall (ba: list ballot) (t : cand ->Q) (p: cand -> list ballot) (bl: list cand) (e: {elected: list cand | length elected <= st}) (h: {hopeful : list cand | NoDup hopeful}) (n: Q)  s,s= state (ba, t, p, bl, e, h, n) -> forall b: ballot, NoDup (proj1_sig (fst b)).
Proof.
 intros ba t p bl e h n s H1 b.
 destruct b as [[b11 [b121 b122]] b2].
 simpl.
  assumption.
Qed.



(*if c is not the first continuing candidate in a ballot then c does not receives it*)
Lemma weakened_list_is_first_notin: forall (t: cand -> Q) (e: {elected:list cand| length elected <= st}) (p: cand -> list ballot)(bl :list cand) c (h: {hopeful: list cand | NoDup hopeful}) (n:Q) ba (d:ballot) (d0:cand) l1 l2, proj1_sig (fst d)= l1++[c]++l2 -> In d0 l1 -> In d0 (proj1_sig h) -> ~ In (proj1_sig (fst d)) (map (fun (d' :ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba)).
Proof.
 intros t e p bl c h n ba d d0 l1 l2 H1 H2 H3.
 induction ba.
 simpl.
 intro.
 auto.
 intro H4.
 specialize (list_eq_dec (cand_eq_dec) (proj1_sig (fst (d))) (proj1_sig (fst a))).
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
 apply (ballot_nodup ba t p bl e h n (state (ba, t, p, bl, e, h, n))).
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
Lemma listballot_fcc: forall ba (t: cand -> Q) (p: cand -> list ballot) (bl: list cand) (e: {elected: list cand | length elected <= st}) (h: {hopeful: list cand | NoDup hopeful}) (n:Q), (forall c, In c (proj1_sig h) -> forall d: ballot, In (proj1_sig (fst d)) (map (fun (d':ballot) => (proj1_sig (fst d'))) (list_is_first_hopeful c (proj1_sig h) ba)) <-> fcc ba (proj1_sig h) c d).
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


(* proof of app property; at every non-final stage of the computation, one rule is applicable*)
Lemma app_FT : app FT_Judgement FT_final FTR.
Proof. 
 unfold app.
 intros p Hnf.
 destruct p. 
 exists initial_step.
 exists (state ((Filter l), nty, nas, nbdy, emp_elec, all_hopeful, (((inject_Z (Z.of_nat (length (Filter l)))) / (1 + inject_Z (Z.of_nat st)) + 1)%Q))).
 split.                                  
 left;auto.
 unfold initial_step.     
 exists l;exists ((Filter l)). exists (((inject_Z (Z.of_nat (length (Filter l)))) / (1 + inject_Z (Z.of_nat st)) + 1)%Q).
 repeat split. 
 specialize (Filter_Permutation_ballot l);intro H_init.
 destruct H_init as [l1 H_init1].
 exists l1. assumption. 
 destruct p as [[[[[[ba t] p] bl] e] h] n].                     
 destruct ba.
  (* case ba = [] *)
 destruct (le_lt_dec (length (proj1_sig e) + length (proj1_sig h)) st) as [ les1 | les2 ].
       (* case length (proj1_sig e) + length h <= st *)
 exists hwin. 
 exists (winners ((proj1_sig e) ++ (proj1_sig h))).
 split. 
 unfold FTR. right;right;right;right;right;left;auto. 
 unfold hwin. 
 exists (proj1_sig e ++ (proj1_sig h)); exists []; exists t; exists p; exists bl; exists e;  exists h. exists n.
 split. reflexivity. 
 split. assumption.
 split. reflexivity.
 reflexivity.
       (* case length (proj1_sig e) + length (proj1_sig h) > st *)
 assert (([]<> (proj1_sig h)) -> existsT d, In d (proj1_sig h) /\  (forall d', In d' (proj1_sig h) -> (t d' <= t d)%Q)).
 apply (list_max_cor cand (proj1_sig h) t).
 assert (forall (q:Q), ((forall c, In c (proj1_sig h) -> (t(c) < q)%Q) + (existsT c: cand, In c (proj1_sig h) /\ (t(c) >= q)%Q))).
 induction (proj1_sig h).
 intro q.
 left;intros.
 contradict H.
 assert (forall a:cand, forall h:list cand, [] <> a::h).
 intros.
 intro.
 inversion H.
 specialize (X (H a l)).
 destruct X.
 destruct a0.
 assert (forall (q:Q), ({(t x < q)%Q} + {(q <= t x)%Q})). intro q1. apply (Qlt_le_dec (t x) q1). 
 intro q2. 
 specialize (H2 q2).
 destruct H2.
 left.
 intros.
 specialize (H1 c H2).
 apply (Qle_lt_trans (t c) (t x) q2).
 auto.
 auto.
 right.
 exists x.
 split.
 auto.
 auto.
 specialize (X0 n).
 destruct X0.
 destruct bl.
 assert ((proj1_sig h) <> []).
 specialize (list_min cand (proj1_sig h) t).
 intro.
 destruct X0.
 destruct (proj1_sig h).
 rewrite <- app_length in les2.
 rewrite app_nil_r in les2.
 specialize (proj2_sig e).
 intro.
 apply le_lt_or_eq in H.
 intuition.
 inversion e0.
 destruct s.
 destruct a.
 intro.
 rewrite H1 in H.
 inversion H.
 destruct X.
 intro.
 rewrite <- H0 in H.
 apply H.
 auto.
 destruct a.
 specialize (list_min cand (proj1_sig h) t).
 intro.
 destruct X.
 rewrite e0 in H.
 contradict H.
 auto.
 destruct s.
 destruct a.
        (*case for elim*)
 exists elim.
 specialize (remc_nodup (proj1_sig h) x0 (proj2_sig h) H2);intro H'1.
 exists (state (p x0, t, emp x0 p,([]:list cand), e, exist _ (remc x0 (proj1_sig h)) H'1, n)).
 split.
 unfold FTR.
 intuition.
 unfold elim.
 exists (p x0).
 exists t.
 exists p. 
 exists (emp x0 p).
 exists e.
 exists h.
 exists (exist _ (remc x0 (proj1_sig h)) H'1).
 exists n.
 split.
 auto.
 split.
 assumption.
 split.
 assumption.
 exists x0.
 split.
 split.
 assumption.
 split.
 apply (remc_ok x0 (proj1_sig h)).
 destruct h as [h1 h2].
 simpl.
 assumption.        
 assumption.
 split.
 auto.
 split.
 unfold emp.
 destruct cand_eq_dec.
 auto.
 contradict n0.
 auto.
 intros.
 unfold emp.
 destruct cand_eq_dec. 
 rewrite e0 in H4.
 contradict H4;auto.
 auto.
 auto.
      (*case for transfer*) 
 exists transfer.
 exists (if (eq_dec_nat (length (proj1_sig e)) st) then winners (proj1_sig e) else state (p c, t, emp c p, bl, e,h,n)).  
 split.
 unfold FTR.
 intuition.
 unfold transfer.
 exists (p c).
 exists t.
 exists p.
 exists (emp c p).
 exists (c::bl).
 exists bl.
 exists h.
 exists e.
 exists n.
 split.
 auto.
 destruct (eq_dec_nat (length (proj1_sig e)) st) as [i | j].
 exists (proj1_sig e).
 split.        
 reflexivity.
 auto.
 split.
 assumption.
 exists bl.
 exists c.
 split.
 split.
 auto.
 split;auto.
 split;auto.
 split.
 unfold emp.
 destruct cand_eq_dec.
 auto.
 contradict n0;auto.
 intros.
 unfold emp.
 destruct cand_eq_dec.
 rewrite e0 in H.
 contradict H;auto.
 auto.
 reflexivity.
 assert (Hypo_2: {st <= length (proj1_sig e)} + {st > length (proj1_sig e)}) by apply (le_lt_dec st (length (proj1_sig e))).
 destruct Hypo_2 as [Hypo3 | Hypo3].
 specialize (le_lt_eq_dec st (length (proj1_sig e)) Hypo3);intro H4.
 destruct H4 as [H5 | H5].
 specialize (proj2_sig e);intro H6.
 omega.
 exists ewin.
 exists (winners (proj1_sig e)).
 split.
 unfold FTR.
 right;right;right;right;right;right;left;auto.
 unfold ewin.
 exists (proj1_sig e);exists ([]:list ballot);exists t;exists p;exists bl;exists e;exists h;exists n.
 repeat split.
 auto.
 specialize (constructing_electable_first e t h n Hypo3 (proj2_sig h));intro Hl. 
 destruct Hl as [l [Hl1 [Hl2 [Hl3 Hl4]]]].
 assert (Hypo5: length ((proj1_sig e)++l)<= st).
 rewrite (app_length (proj1_sig e) l).
 omega.
     (*case elect*)
 exists elect.
 specialize (Removel_nodup l (proj1_sig h) (proj2_sig h));intro H'2.
 exists (state ([]:list ballot, t, update_pile p t l n, bl++l, exist _ ((proj1_sig e)++l) Hypo5, exist _ (Removel l (proj1_sig h)) H'2, n)).
 split.
 unfold FTR.
 intuition.
 destruct Hl4 as [Hl4_1 Hl4_2].
 assert (Hypo6: [] <> (proj1_sig h)).
 intro H6.
 rewrite<- H6 in les2.
 simpl in les2.
 omega. 
 assert (Hypo7: {length l < st - length (proj1_sig e)} + {length l = st - length (proj1_sig e)}).
 rewrite app_length in Hypo5.
 specialize (le_lt_eq_dec (length (proj1_sig e) + length l) st Hypo5);intro H7.
 destruct H7 as [H7_1 |H7_2].
 left.
 omega.
 right.
 omega.
 assert (Hypo8: l <> []).
 destruct Hypo7 as [Hypo7_1 | Hypo7_2].
 destruct s as [d s1].
 destruct s1 as [s1_1 s1_2].
 specialize (Hl4_2 d).
 assert (Hypo8: In d (proj1_sig h) /\ (n <= t d)%Q /\ length l < st - length (proj1_sig e)).
 split;auto.
 specialize (Hl4_2 Hypo8).
 intro H5.
 rewrite H5 in Hl4_2.
 inversion Hl4_2.
 intro H5.
 rewrite H5 in Hypo7_2.
 simpl in Hypo7_2.
 omega.
 unfold elect.
 exists [];exists t;exists p;exists (update_pile p t l n);exists bl;exists (bl++l);exists (exist _ (Removel l (proj1_sig h)) H'2);exists h;exists (exist _ (proj1_sig e) (proj2_sig e));exists (exist _ ((proj1_sig e)++l) Hypo5);exists n.
 split.
 assert (Hypo9: e = exist (fun elected : list cand => length elected <= st) 
                           (proj1_sig e) (proj2_sig e)).
 destruct e.
 simpl.
 trivial.
 rewrite Hypo9.
 auto.
 exists l.
 split.
 split.
 assumption.
 assert (Hypo10: e = exist (fun elected : list cand => length elected <= st) 
                            (proj1_sig e) (proj2_sig e)).
 destruct e.
 simpl.
 trivial.
 split.
 rewrite Hypo10.
 simpl.
 assumption.
 split.
 intros c Hc.
 specialize (Hl1 c Hc).
 auto.
 split.
 assumption.
 split.
 unfold Leqe.
 apply (Permutation_app).
 apply (nodup_permutation). 
 intros x H5.
 specialize (Hl1 x H5).
 destruct Hl1 as [Hl1_1 Hl1_2].
 assumption.
 assumption.
 destruct h as [h1 h2].
 simpl.
 auto.
 split.
 apply Permutation_refl.
 split.
 intros c1 H6.
 unfold update_pile.
 destruct (cand_in_dec c1 l) as [i | j].
 trivial.
 contradiction j.
 split.
 intros c' H7.
 unfold update_pile.
 destruct (cand_in_dec c' l) as [ i | j].
 contradiction H7.
 auto.
 reflexivity.
 auto.
  (*case for count*)
 exists count.
 exists (state ([], fun (c:cand) =>  if (cand_in_dec c (proj1_sig h)) then sum (p (c) ++ (list_is_first_hopeful c (proj1_sig h) (b::ba))) else (t c), fun (c:cand) => (if (cand_in_dec c (proj1_sig h)) then( p (c) ++ list_is_first_hopeful c (proj1_sig h) (b::ba)) else (p c)), bl, e, h,n)).
 split.
 unfold FTR.
 intuition.
 unfold count.
 exists (b::ba).
 exists t.
 exists (fun (c:cand) => if (cand_in_dec c (proj1_sig h)) then (sum ( p(c) ++ list_is_first_hopeful c (proj1_sig h) (b::ba))) else (t c)).
 exists p.
 exists (fun (c:cand) => if (cand_in_dec c (proj1_sig h)) then p (c) ++ list_is_first_hopeful c (proj1_sig h) (b::ba) else (p c)). 
 exists bl.
 exists h.
 exists e.
 exists n.
 split.
 auto.
 split.
 intro H2.
 inversion H2.
 split.
 intros c.
 destruct (cand_in_dec c (proj1_sig h)) as [ i| j].
 exists (list_is_first_hopeful c (proj1_sig h) (b::ba)).
 split.
 auto.
 split.
 intro b0.
 specialize (listballot_fcc (b::ba) t p bl e h n c i b0);intro H3.
 assumption.
 auto.
 split.
 trivial.
 reflexivity.
 trivial.
 exfalso.
 apply Hnf.
 unfold FT_final.
 exists l. 
 auto.
Qed.



Definition hunion_count:= termination (FT_Judgement ) (FT_final ) (final_dec ) (FT_WFO ) (FT_wfo ) FT_wfo_wf (FT_m ) (FTR ) (dec_FT ) (app_FT). 

*)

