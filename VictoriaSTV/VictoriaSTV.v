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
Require Export Parameters.
Require Import FrameBase.
Require Export Instantiation.
Import Instantiate.
Import M.
Import QSort.

Module VicSTV.

Section Victoria.

Definition VIC_InitStep (prem :FT_Judgement) (conc :FT_Judgement): Prop :=
 exists ba ba',  
  ((prem = (initial  ba)) /\
  (ba' = (Filter ba)) /\
  (conc = state  (ba', [nty], nas, (nbdy, nbdy), emp_elec , all_hopeful))).

Definition VIC_count (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
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

Definition VIC_hwin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h,                            
   prem = state (ba, t, p, bl, e, h) /\           
   length (proj1_sig e) + length (proj1_sig h) <= st /\ 
   w = (proj1_sig e) ++ (proj1_sig h) /\                        
   conc = winners (w).

Definition VIC_ewin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h,                    (** elected win **)
   prem = state (ba, t, p, bl, e, h) /\   (* if at any time *)
   length (proj1_sig e) = st /\             (* we have as many elected candidates as seats *) 
   w = (proj1_sig e) /\                        (* and the winners are precisely the electeds *)
   conc = winners (w).                      (* they are declared the winners *)

Definition VIC_elim (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists  t p e h nh bl2,                    
   prem = state ([], t, p, ([], bl2), e, h) /\         
   length (proj1_sig e) + length (proj1_sig h) > st /\ 
   (forall c, In c (proj1_sig h) -> (hd nty t(c) < quota)%Q) /\ 
   exists c,                                            
     ((forall d, In d (proj1_sig h) -> (hd nty t(c) <= hd nty t(d)))%Q /\            
     eqe c (proj1_sig nh) (proj1_sig h) /\                                                          
   conc = state ([], t, p, ([], c::bl2), e, nh)). 

Definition VIC_transfer (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
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

Definition VIC_elect (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
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

Definition VIC_TransferElected2 (prem: FT_Judgement) (conc: FT_Judgement) :=
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

Definition VIC_TransferElim (prem: FT_Judgement) (conc: FT_Judgement) :=
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

Lemma VICInitStep_SanityCheck_App : SanityCheck_Initial_App VIC_InitStep.
Proof.
 unfold SanityCheck_Initial_App.  
 intros.
 exists (state (Filter ba, [nty], nas, (nbdy, nbdy), emp_elec, all_hopeful)). 
 split. auto.
 unfold VIC_InitStep.
 exists ba.
 exists (Filter ba).
 split. assumption.
 split;auto. 
Qed. 

Lemma VICInitStep_SanityCheck_Red: SanityCheck_Initial_Red VIC_InitStep.
 unfold SanityCheck_Initial_Red.
 intros.
 unfold VIC_InitStep in H.
 destruct H as [ba [ba' H1]]. 
 exists ba. exists ba'. exists [nty]. exists nas. exists (nbdy, nbdy). exists emp_elec. exists all_hopeful.
 split;auto.
 intuition.
 intuition.
Qed.

Hypothesis Bl_hopeful_NoIntersect : forall j: FT_Judgement, forall ba t p bl e h, j = state (ba,t,p,bl,e,h) ->
 (forall c, In c (snd bl) -> ~ In c (proj1_sig h)) * (forall c, In c (fst bl) -> ~ In c (snd bl)).

Lemma VICCount_SanityCheck_App : SanityCheck_Count_App VIC_count.
Proof.
 unfold SanityCheck_Count_App. 
 intros.
 exists (state ([], (fun (c:cand) =>  if (cand_in_dec c (proj1_sig h)) then SUM (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (hd nty t) c) :: t, fun (c:cand) => (if (cand_in_dec c (proj1_sig h)) then (p (c) ++ [list_is_first_hopeful c (proj1_sig h) ba]) else (p c)), bl, e, h)).
 unfold VIC_count.
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

Lemma VICCount_SanityCheck_Red: SanityCheck_Count_Red VIC_count.
 Proof.
 unfold SanityCheck_Count_Red.
 intros.
 unfold VIC_count in H.
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


Lemma  VICHwin_SanityCheck_App : SanityCheck_Hwin_App VIC_hwin.                           
Proof.
 unfold SanityCheck_Hwin_App.
 intros.
 unfold VIC_hwin.
 exists (winners ((proj1_sig e) ++ (proj1_sig h))).
 exists ((proj1_sig e) ++ (proj1_sig h)).
 exists ba; exists t; exists p; exists bl; exists e; exists h.  
 auto.
Qed.

Lemma VICHwin_SanityCheck_Red : SanityCheck_Hwin_Red VIC_hwin.
Proof.
 unfold SanityCheck_Hwin_Red.
 intros.
 unfold VIC_hwin in H. 
 destruct H as [w [ba [t [p [bl [e [h H1]]]]]]]. 
 exists w; exists ba; exists t; exists p; exists bl; exists e; exists h. 
 intuition.
Qed.

Lemma VICEwin_SanityCheck_App : SanityCheck_Ewin_App VIC_ewin.
Proof.
 unfold SanityCheck_Ewin_App.
 intros.
 unfold VIC_ewin.
 exists (winners (proj1_sig e)). 
 exists (proj1_sig e). exists ba. exists t. exists p. exists bl. exists e. exists h.
 intuition.
Qed.

Lemma VICEwin_SanityCheck_Red : SanityCheck_Ewin_Red VIC_ewin.
Proof.
 unfold SanityCheck_Ewin_Red.
 intros.
 unfold VIC_ewin in H.
 destruct H as [w [ba [t [p [bl [e [h H1]]]]]]].
 exists w. exists ba. exists t. exists p. exists bl. exists e. exists h. 
 intuition.
 rewrite <- H0.
 assumption.
Qed.

Lemma VICElim_SanityCheck_App : SanityCheck_Elim_App VIC_elim.
Proof.
 unfold SanityCheck_Elim_App.
 intros.
 unfold VIC_elim.
 specialize (list_min cand (proj1_sig h) (hd nty t)). intro min_hopeful.
 destruct min_hopeful.
 rewrite e0 in H0.
 destruct H0 as [H01 H02].
 destruct e.
 simpl in H01.
 omega.
 destruct s as [min [s1 s2]].
 specialize (remc_nodup (proj1_sig h) min (proj2_sig h) s1);intro H'1.
 exists (state ([], t, p,
                                                ([], min:: bl2), e, exist _ (remc min (proj1_sig h)) H'1)). 
 exists t. exists p. exists e. exists h. 
 exists (exist _ (remc min (proj1_sig h)) H'1).
 intuition.
 exists bl2.
 intuition.
 simpl.
 exists min.
 intuition.
 apply (remc_ok min (proj1_sig h) (proj2_sig h) s1).
Qed.

Lemma VICElim_SanityCheck_Red : SanityCheck_Elim_Red VIC_elim.
 Proof.
 unfold SanityCheck_Elim_Red.
 intros. 
 unfold VIC_elim in H.
 destruct H as [t [p [e [h [nh [bl2 H1]]]]]].
 destruct H1 as [H11 [H12 [H13 H14]]].
 destruct H14 as [weakest H141]. 
 exists ([]: list ballot). exists t. exists p. exists p. exists e. exists h. exists nh.  
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
 exists (weakest :: bl2).
 intuition.
Qed.

Lemma VICTransfer_SanityCheck_App : SanityCheck_Transfer1_App VIC_transfer.
Proof.
 unfold SanityCheck_Transfer1_App.
 intros.
 unfold VIC_transfer.
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
 destruct (cand_eq_dec c c) as [i | j]. reflexivity.
 contradict j. auto.
 destruct (cand_eq_dec d c) as [i | j].
 contradict i. assumption.
 auto.
Qed.

Lemma VICTransfer_SanityCheck_Red : SanityCheck_Transfer_Red VIC_transfer.
 Proof.
 unfold SanityCheck_Transfer_Red.
 intros.
 unfold VIC_transfer in H.
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

Lemma VICElect_SanityCheck_App : SanityCheck_Elect_App VIC_elect.
Proof.
 unfold SanityCheck_Elect_App.
 intros.
 unfold VIC_elect.
 specialize (constructing_electable_first).
 intro H1.
  (*I am changing X to H0*)
 destruct H0 as [c [X1 X2]].
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
 destruct (cand_in_dec c0 listElected) as [i | j].
 trivial.
 contradict j. assumption.
 unfold update_pile.
 destruct (cand_in_dec c0 listElected) as [i |j].
 contradict i.
 assumption.
 auto.
Qed.

Lemma VICElect_SanityCheck_Red : SanityCheck_Elect_Red VIC_elect.
Proof.
 unfold SanityCheck_Elect_Red.
 intros.
 unfold VIC_elect in H.
 destruct H as [t [p [np [bl [nbl [nh [h [e [ne H1]]]]]]]]].
 exists t. exists p; exists np. exists bl. exists nbl. exists e. exists ne. exists nh. exists h.
 destruct H1 as [H11 H12].
 destruct H12 as [l H121].
 intuition.
 unfold Leqe in H4.
 specialize (Permutation_length H4). intro Permut_length.
 rewrite Permut_length.
 rewrite  app_length.
 specialize (list_nonempty_type cand l H1). intro X.
 destruct X as [c [l' HX]].
 rewrite HX.
 simpl.
 omega.
 unfold Leqe in H5.
 specialize (Permutation_length H5). intro.
 rewrite H8.
 rewrite app_length.
 specialize (list_nonempty_type cand l H1). intro X.
 destruct X as [c [l' HX]].
 rewrite HX.
 simpl.
 omega.
Qed.

Lemma VICTran2_SanityCheck_App : SanityCheck_Transfer2_App VIC_TransferElected2. 
Proof.
 unfold SanityCheck_Transfer2_App.
 intros. 
 unfold VIC_TransferElected2.
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
 destruct (cand_eq_dec Headbl1 Headbl1) as [i | j].
 reflexivity.
 contradict j.  auto.
 destruct (cand_eq_dec d Headbl1) as [i | j].
 contradict i.
 auto.
 reflexivity.
Qed.

Lemma VICTran2_SanityCheck_Red : SanityCheck_Transfer_Red VIC_TransferElected2.
Proof.
 unfold SanityCheck_Transfer_Red.
 intros.
 unfold VIC_TransferElected2 in H.
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

Hypothesis Bl_NoDup : forall j: FT_Judgement, forall ba t p bl e h, 
  j = state (ba,t,p,bl,e,h) -> NoDup (snd bl).

Lemma VIC_TransferElim_SanityCheck_App : SanityCheck_Transfer3_App VIC_TransferElim.
Proof.
 unfold SanityCheck_Transfer3_App.
 intros.
 destruct H0 as [H1 [H2 [H3 H4]]].
 unfold VIC_TransferElim.
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
 contradiction i. reflexivity.
Qed.

Lemma concat_app : forall (A:Type) (l1: list (list A)) l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
Proof.
  intros.
  induction l1 as [|x l1 IH]. induction l2. simpl.
  reflexivity. simpl. auto.
  simpl. rewrite IH; apply app_assoc.
Qed.
 
Lemma VIC_TransferElim_SanityCheck_Red: SanityCheck_Transfer_Red VIC_TransferElim.
Proof.
 unfold SanityCheck_Transfer_Red. 
 intros.
 unfold VIC_TransferElim in H.
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

Variable bs: list ballot.

Definition VicSTV := (mkSTV (quota)  
    (VIC_InitStep) (VICInitStep_SanityCheck_App) (VICInitStep_SanityCheck_Red) 
    (VIC_count) (VICCount_SanityCheck_App) (VICCount_SanityCheck_Red)
    (VIC_transfer) (VICTransfer_SanityCheck_App) (VICTransfer_SanityCheck_Red)
    (VIC_TransferElected2) (VICTran2_SanityCheck_App) (VICTran2_SanityCheck_Red)
    (VIC_TransferElim) (VIC_TransferElim_SanityCheck_App) (VIC_TransferElim_SanityCheck_Red)
    (VIC_elect) (VICElect_SanityCheck_App) (VICElect_SanityCheck_Red)
    (VIC_elim) (VICElim_SanityCheck_App) (VICElim_SanityCheck_Red)
    (VIC_hwin) (VICHwin_SanityCheck_App) (VICHwin_SanityCheck_Red)
    (VIC_ewin) (VICEwin_SanityCheck_App) (VICEwin_SanityCheck_Red)).

Lemma init_stages_R_initial : ~ FT_final (initial (Filter bs)).
Proof.
 intro.
 unfold FT_final in H.
 destruct H.
 inversion H.
Qed.
 
Definition Vic_Termination := M.Termination bs (initial (Filter bs)) init_stages_R_initial VicSTV.


End Victoria.

Extraction Language Haskell.
Extraction "Vic.hs" Vic_Termination.
  
End VicSTV.
