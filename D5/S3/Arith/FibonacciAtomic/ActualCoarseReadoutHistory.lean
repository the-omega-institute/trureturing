/- GID: D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fresh coarse divergence and saturated common-history obstruction. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
import Mathlib.Data.List.Infix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- The leaf labels remain distinct; branch and absent have the same coarse reply. -/
def kappa : Reply → Option Bool
  | .alpha => some true
  | .beta => some false
  | .branch | .absent => none

local notation "κ" => kappa

/-- Coarsening retains every actual address, its order, and repeated requests. -/
def kappa_hist (h : Hist (fun _ : Address => Reply)) : Hist (fun _ : Address => Option Bool) :=
  h.map (fun a => ⟨a.1, κ a.2⟩)

local notation "κHist" => kappa_hist

/-- The original selector depends only on its coarse chronological history. -/
def CoarseObservable (p : Policy) : Prop :=
  ∀ h k, κHist h = κHist k → p h = p k

/-- Distinct nonconflicting positive trees diverge at a fresh coarse query.
If both have already paid a nonleaf on a shared prefix, one final excess is at least two. -/
theorem shared_history_obstruction (π : Strategy) (observable : CoarseObservable π.policy)
    (U V : Source) (positiveU : Positive U) (_positiveV : Positive V)
    (different : U ≠ V) (nc : Nonconflict U V)
    (h : Hist (fun _ : Address => Option Bool))
    (prefixU : h.IsPrefix (κHist (terminal π U).1))
    (prefixV : h.IsPrefix (κHist (terminal π V).1)) :
    ∃ (s : Hist (fun _ : Address => Option Bool)) (q : Address),
      (h ++ s ++ [(⟨q, leafLabel U q⟩ :
        Sigma (fun _ : Address => Option Bool))]).IsPrefix (κHist (terminal π U).1) ∧
      (h ++ s ++ [(⟨q, leafLabel V q⟩ :
        Sigma (fun _ : Address => Option Bool))]).IsPrefix (κHist (terminal π V).1) ∧
      leafLabel U q ≠ leafLabel V q ∧
      q ∉ ((h ++ s).map Sigma.fst).toFinset ∧
      (q ∉ leafAddresses U ∨ q ∉ leafAddresses V) ∧
      ((((h.map Sigma.fst).toFinset \ leafAddresses U).Nonempty ∧
         ((h.map Sigma.fst).toFinset \ leafAddresses V).Nonempty) →
        2 ≤ (paid (terminal π U).1 \ leafAddresses U).card ∨
        2 ≤ (paid (terminal π V).1 \ leafAddresses V).card) := by
  classical
  have label (W : Source) (q : Address) : κ (readout q W) = leafLabel W q := by
    rfl
  have compare : ∀ (n m : Nat) (a b : Hist (fun _ : Address => Reply))
      (t u : Hist (fun _ : Address => Reply)) (x y : Bool)
      (g : Hist (fun _ : Address => Option Bool)),
      κHist a = κHist b → execute readout π.policy n a U = some (t,x) →
      execute readout π.policy m b V = some (u,y) →
      g.IsPrefix (κHist t) → g.IsPrefix (κHist u) →
      κHist t = κHist u ∨ ∃ s q,
        (g ++ s ++ [(⟨q, leafLabel U q⟩ :
          Sigma (fun _ : Address => Option Bool))]).IsPrefix (κHist t) ∧
        (g ++ s ++ [(⟨q, leafLabel V q⟩ :
          Sigma (fun _ : Address => Option Bool))]).IsPrefix (κHist u) ∧
        leafLabel U q ≠ leafLabel V q := by
    intro n
    induction n with
    | zero => intro m a b t u x y g same runU; simp [execute] at runU
    | succ n ih =>
      intro m a b t u x y g same runU runV preU preV
      cases m with
      | zero => simp [execute] at runV
      | succ m =>
        have action := observable a b same
        cases step : π.policy a with
        | inr z =>
          have other : π.policy b = .inr z := action.symm.trans step
          simp only [execute, step, Option.some.injEq, Prod.mk.injEq] at runU
          simp only [execute, other, Option.some.injEq, Prod.mk.injEq] at runV
          rcases runU with ⟨rfl,rfl⟩
          rcases runV with ⟨rfl,rfl⟩
          exact Or.inl rfl
        | inl q =>
          have other : π.policy b = .inl q := action.symm.trans step
          simp only [execute, step, Option.map_eq_some_iff] at runU
          simp only [execute, other, Option.map_eq_some_iff] at runV
          obtain ⟨⟨t',x'⟩,runU,eU⟩ := runU
          obtain ⟨⟨u',y'⟩,runV,eV⟩ := runV
          cases eU; cases eV
          change g.IsPrefix (⟨q, κ (readout q U)⟩ :: κHist t') at preU
          change g.IsPrefix (⟨q, κ (readout q V)⟩ :: κHist u') at preV
          by_cases equal : leafLabel U q = leafLabel V q
          · have extended : κHist (a ++ [⟨q,readout q U⟩]) =
                κHist (b ++ [⟨q,readout q V⟩]) := by
              simp only [kappa_hist, List.map_append, List.map_cons, List.map_nil]
              change κHist a ++ [⟨q,κ (readout q U)⟩] =
                κHist b ++ [⟨q,κ (readout q V)⟩]
              rw [same, label, label, equal]
            cases g with
            | nil =>
              rcases ih m _ _ t' u' x' y' [] extended runU runV
                  List.nil_prefix List.nil_prefix with joined | ⟨s,r,hs,ht,hr⟩
              · left
                change (⟨q,κ (readout q U)⟩ :: κHist t') =
                  (⟨q,κ (readout q V)⟩ :: κHist u')
                rw [label, label, equal, joined]
              · refine Or.inr ⟨⟨q,leafLabel U q⟩ :: s,r,?_,?_,hr⟩
                · simpa only [List.nil_append, List.cons_append, kappa_hist, List.map_cons, label]
                    using (List.cons_prefix_cons.mpr ⟨rfl,hs⟩ :
                      (⟨q,leafLabel U q⟩ : Sigma (fun _ : Address => Option Bool)) ::
                        (_ ++ _) <+: _ :: _)
                · simpa only [List.nil_append, List.cons_append, kappa_hist, List.map_cons, label, equal]
                    using (List.cons_prefix_cons.mpr ⟨rfl,ht⟩ :
                      (⟨q,leafLabel V q⟩ : Sigma (fun _ : Address => Option Bool)) ::
                        (_ ++ _) <+: _ :: _)
            | cons c g =>
              obtain ⟨headU,tailU⟩ := List.cons_prefix_cons.mp preU
              obtain ⟨headV,tailV⟩ := List.cons_prefix_cons.mp preV
              rcases ih m _ _ t' u' x' y' g extended runU runV tailU tailV with
                joined | ⟨s,r,hs,ht,hr⟩
              · left
                simp only [kappa_hist, List.map_cons, label, equal]
                exact congrArg _ joined
              · refine Or.inr ⟨s,r,?_,?_,hr⟩
                · simpa only [List.cons_append, kappa_hist, List.map_cons, ← headU]
                    using (List.cons_prefix_cons.mpr ⟨rfl,hs⟩ : c :: _ <+: c :: _)
                · simpa only [List.cons_append, kappa_hist, List.map_cons, ← headV]
                    using (List.cons_prefix_cons.mpr ⟨rfl,ht⟩ : c :: _ <+: c :: _)
          · have empty : g = [] := by
              cases g with
              | nil => rfl
              | cons c g =>
                have hU := (List.cons_prefix_cons.mp preU).1
                have hV := (List.cons_prefix_cons.mp preV).1
                have response := congrArg Sigma.snd (hU.symm.trans hV)
                exact False.elim (equal (by simpa only [label] using response))
            subst g
            refine Or.inr ⟨[],q,?_,?_,equal⟩
            · change [(⟨q,leafLabel U q⟩ : Sigma (fun _ : Address => Option Bool))] <+:
                ⟨q,κ (readout q U)⟩ :: κHist t'
              rw [label]
              exact ⟨_,rfl⟩
            · change [(⟨q,leafLabel V q⟩ : Sigma (fun _ : Address => Option Bool))] <+:
                ⟨q,κ (readout q V)⟩ :: κHist u'
              rw [label]
              exact ⟨_,rfl⟩
  have actual (W : Source) : execute readout π.policy
      (Classical.choose (π.correct W)) [] W = some (terminal π W) :=
    (Classical.choose_spec (Classical.choose_spec (π.correct W))).1
  have truth : ∀ (n : Nat) (a t : Hist (fun _ : Address => Reply)) (W : Source) (b : Bool),
      execute readout π.policy n a W = some (t,b) →
      ∀ r ∈ t, r.2 = readout r.1 W := by
    intro n
    induction n with
    | zero => intro a t W b run; simp [execute] at run
    | succ n ih =>
      intro a t W b run
      cases step : π.policy a with
      | inr z =>
        simp only [execute, step, Option.some.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl,rfl⟩
        simp
      | inl q =>
        simp only [execute, step, Option.map_eq_some_iff] at run
        obtain ⟨⟨t',b'⟩,run,e⟩ := run
        cases e
        intro r member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · exact ih _ _ _ _ run r member
  have coarse_truth (W : Source) : ∀ r ∈ κHist (terminal π W).1,
      r.2 = leafLabel W r.1 := by
    intro r member
    obtain ⟨a,rawMember,rfl⟩ := List.mem_map.mp member
    change κ a.2 = leafLabel W a.1
    rw [truth _ _ _ _ _ (actual W) a rawMember, label]
  have address_map (t : Hist (fun _ : Address => Reply)) :
      (κHist t).map Sigma.fst = t.map Sigma.fst := by
    simp only [kappa_hist, List.map_map, Function.comp_def]
  have prefix_paid (W : Source) (g : Hist (fun _ : Address => Option Bool))
      (pre : g.IsPrefix (κHist (terminal π W).1)) :
      (g.map Sigma.fst).toFinset ⊆ paid (terminal π W).1 := by
    intro q member
    change q ∈ ((terminal π W).1.map Sigma.fst).toFinset
    rw [← address_map]
    exact List.mem_toFinset.mpr ((pre.map Sigma.fst).subset (List.mem_toFinset.mp member))
  have leaf_injective (r t : Reply) (b : Bool) (hr : κ r = some b)
      (same : κ r = κ t) : r = t := by
    cases r <;> cases t <;>
      simp only [kappa, Option.some.injEq, reduceCtorEq] at hr same ⊢
  have unequal : κHist (terminal π U).1 ≠ κHist (terminal π V).1 := by
    intro joined
    apply different
    exact (source_foundation.2.2.1 U V (by
      intro q member
      have paidU := source_foundation.2.2.2.2.1 π U positiveU
        (List.mem_toFinset.mpr member)
      obtain ⟨a,memberA,addressA⟩ := List.mem_map.mp (List.mem_toFinset.mp paidU)
      have memberCoarse : (⟨a.1,κ a.2⟩ : Sigma (fun _ : Address => Option Bool)) ∈
          κHist (terminal π U).1 := List.mem_map.mpr ⟨a,memberA,rfl⟩
      have same_label : leafLabel U q = leafLabel V q := by
        have hu := coarse_truth U _ memberCoarse
        rw [joined] at memberCoarse
        have hv := coarse_truth V _ memberCoarse
        simpa only [addressA] using hu.symm.trans hv
      obtain ⟨b,hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 U).2 q |>.mp
        (show q ∈ leafAddresses U from List.mem_toFinset.mpr member)
      exact (leaf_injective (readout q U) (readout q V) b
        (by simpa only [label] using hb) (by simpa only [label] using same_label)).symm)).symm
  rcases compare _ _ [] [] (terminal π U).1 (terminal π V).1
      (terminal π U).2 (terminal π V).2 h rfl (actual U) (actual V) prefixU prefixV with
    joined | ⟨s,q,preU,preV,distinct⟩
  · exact False.elim (unequal joined)
  · have sharedU : (h ++ s).IsPrefix (κHist (terminal π U).1) :=
      (List.prefix_append _ _).trans preU
    have sharedV : (h ++ s).IsPrefix (κHist (terminal π V).1) :=
      (List.prefix_append _ _).trans preV
    have fresh : q ∉ ((h ++ s).map Sigma.fst).toFinset := by
      intro member
      obtain ⟨r,memberR,addressR⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      have hu := coarse_truth U r (sharedU.subset memberR)
      have hv := coarse_truth V r (sharedV.subset memberR)
      exact distinct (by simpa only [addressR] using hu.symm.trans hv)
    have nonleaf : q ∉ leafAddresses U ∨ q ∉ leafAddresses V := by
      by_contra both
      push Not at both
      obtain ⟨a,ha⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 U).2 q |>.mp both.1
      obtain ⟨b,hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 V).2 q |>.mp both.2
      have same :=
        (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 U V).2.2.mp nc q a b ha hb
      exact distinct (ha.trans (congrArg some same) |>.trans hb.symm)
    refine ⟨s,q,preU,preV,distinct,fresh,nonleaf,?_⟩
    intro saturated
    have two (W : Source)
        (pre : (h ++ s ++ [(⟨q,leafLabel W q⟩ :
          Sigma (fun _ : Address => Option Bool))]).IsPrefix
        (κHist (terminal π W).1)) (notLeaf : q ∉ leafAddresses W)
        (old : ((h.map Sigma.fst).toFinset \ leafAddresses W).Nonempty) :
        2 ≤ (paid (terminal π W).1 \ leafAddresses W).card := by
      obtain ⟨r,memberR⟩ := old
      have prefixH : h.IsPrefix (κHist (terminal π W).1) :=
        (List.prefix_append h s).trans ((List.prefix_append (h ++ s) _).trans pre)
      have oldPaid := prefix_paid W h prefixH (Finset.mem_sdiff.mp memberR).1
      have newPaid : q ∈ paid (terminal π W).1 := by
        apply prefix_paid W _ pre
        simp
      have differentAddress : r ≠ q := by
        intro eq
        apply fresh
        subst r
        apply List.mem_toFinset.mpr
        rw [List.map_append]
        exact List.mem_append_left _ (List.mem_toFinset.mp (Finset.mem_sdiff.mp memberR).1)
      have bound := Finset.one_lt_card.mpr
        ⟨r,Finset.mem_sdiff.mpr ⟨oldPaid,(Finset.mem_sdiff.mp memberR).2⟩,
         q,Finset.mem_sdiff.mpr ⟨newPaid,notLeaf⟩,differentAddress⟩
      omega
    exact nonleaf.elim (fun hn => Or.inl (two U preU hn saturated.1))
      (fun hn => Or.inr (two V preV hn saturated.2))

end D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory
