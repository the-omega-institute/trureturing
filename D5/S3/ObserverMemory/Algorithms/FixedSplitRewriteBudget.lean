/- GID: D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed noncentral split has sharp worst rewrite budget one or two. -/

import D5.S3.ObserverMemory.Algorithms.ControlRewriteDirectionalBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedSplitRewriteBudget

open D5.S3.ObserverMemory.Algorithms.InitializedControlProtocol
open D5.S3.ObserverMemory.Algorithms.ControlRewriteDirectionalBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
open D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
attribute [local instance] Classical.propDecidable
universe u v w

/-- Control restricted to one of the original summands. -/
def controlRestriction {d : Nat} (S : Submodule (ZMod 2) (Source d)) :
    S →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.snd (ZMod 2) (Fin d → ZMod 2) (ZMod 2)).comp S.subtype

/-- The exact one-operation rewrite cost for this fixed split and data column. -/
noncomputable def splitCost {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) (i : Fin d) : Nat :=
  rewriteCost (controlRestriction A) (controlRestriction B)
    (A.projectionOnto B split (Pi.single i 1, 0))
    (B.projectionOnto A split.symm (Pi.single i 1, 0))

/-- Worst rewrite over the original data alphabet, with the split held fixed. -/
noncomputable def Cstar {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) : Nat := Finset.univ.sup (splitCost split)

/-- A uniform initial-rewrite budget ranges over compliant sender-local
protocols, and retains correctness for both prescribed original projections. -/
def InitialRewriteBudget {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) (K : Nat) : Prop :=
  ∀ i : Fin d, ∃ p : EndpointProtocol A B A B,
    RewriteCorrect (controlRestriction A) (controlRestriction B)
      (A.projectionOnto B split (Pi.single i 1, 0))
      (B.projectionOnto A split.symm (Pi.single i 1, 0)) id id p ∧
    ∀ a b n t, execute answer p.policy n [] (a, b) = some (t, ()) → t.length ≤ K

/-- One natural bound covers every source initialization and every finite word.
The cumulative sum directly reuses the established action-graph cost definition. -/
def UniformCumulativeBudget {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    {split : IsCompl A B} {MA : Type u} {MB : Type v} {Root : Type w}
    (C : Controller split MA MB Root) (K : Nat) : Prop :=
  ∀ a b word, Comm C.step C.cost (C.initial a b) word ≤ K

set_option maxHeartbeats 1000000 in
-- The fixed-split column argument and its live protocol consumer are proved together.
/-- For the same fixed noncentral split, the sharp worst rewrite budget is
one when control belongs to one side and two when both restrictions are
nonzero. Some rewrite is paid. The least-budget clause consumes the live
per-execution directional theorem; it is the initial-rewrite supplier for
the persistent controller's cumulative-budget lower bound. -/
theorem fixed_split_rewrite_budget (d : Nat) (_hd : 2 ≤ d)
    (A B : Submodule (ZMod 2) (Source d)) (split : IsCompl A B)
    (hA : 0 < Module.finrank (ZMod 2) A) (hB : 0 < Module.finrank (ZMod 2) B) :
    (controlRestriction A = 0 → Cstar split = 1) ∧
    (controlRestriction B = 0 → Cstar split = 1) ∧
    (controlRestriction A ≠ 0 → controlRestriction B ≠ 0 → Cstar split = 2) ∧
    (∃ i : Fin d, 0 < splitCost split i) ∧
    IsLeast {K : Nat | InitialRewriteBudget split K} (Cstar split) ∧
    (∀ {MA : Type u} {MB : Type v} {Root : Type w} (C : Controller split MA MB Root)
      (K : Nat), UniformCumulativeBudget C K → Cstar split ≤ K ∧
      ∀ a b (i : Fin d),
        directionDemand (A.projectionOnto B split (Pi.single i 1, 0))
          (controlRestriction B) ≤
            rightCount (C.trace (.rewrite i) (C.initial a b)) ∧
        directionDemand (B.projectionOnto A split.symm (Pi.single i 1, 0))
          (controlRestriction A) ≤
            leftCount (C.trace (.rewrite i) (C.initial a b))) := by
  classical
  let pA := A.projectionOnto B split
  let pB := B.projectionOnto A split.symm
  let ellA := controlRestriction A
  let ellB := controlRestriction B
  let e : Fin d → Source d := fun i => (Pi.single i 1, 0)
  have binary (q : ZMod 2) : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
  have data_ext {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
      (F : Source d →ₗ[ZMod 2] T) (hz : ∀ i, F (e i) = 0)
      (z : Source d) (hc : z.2 = 0) : F z = 0 := by
    let incl := LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)
    have hF : F.comp incl = 0 := by
      apply (Pi.basisFun (ZMod 2) (Fin d)).ext
      intro i
      simpa [incl, e] using hz i
    have he : z = incl z.1 := Prod.ext rfl hc
    rw [he]
    exact LinearMap.congr_fun hF z.1
  have columns (i : Fin d) : ellA (pA (e i)) + ellB (pB (e i)) = 0 := by
    change ((A.projection B split (e i)) + (B.projection A split.symm (e i))).2 = 0
    rw [Submodule.projection_add_projection_eq_self split]
  have nonzero_control : ellA ≠ 0 ∨ ellB ≠ 0 := by
    by_contra h
    push Not at h
    have he := congrArg Prod.snd
      (Submodule.projection_add_projection_eq_self split ((0, 1) : Source d))
    change ellA (pA (0, 1)) + ellB (pB (0, 1)) = 1 at he
    rw [h.1, h.2] at he
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) he
  have bound (i : Fin d) : splitCost split i ≤ 2 := by
    unfold splitCost rewriteCost directionDemand
    split_ifs <;> omega
  have maxBound : Cstar split ≤ 2 := Finset.sup_le (fun i _ => bound i)
  have leftColumn (hzero : ellA = 0) : ∃ i, pA (e i) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hA
    have hc : (a : Source d).2 = 0 := by
      change ellA a = 0
      rw [hzero]
      rfl
    have he := data_ext pA h a.val hc
    rw [Submodule.projectionOnto_apply_left] at he
    exact ha he
  have rightColumn (hzero : ellB = 0) : ∃ i, pB (e i) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨b, hb⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hB
    have hc : (b : Source d).2 = 0 := by
      change ellB b = 0
      rw [hzero]
      rfl
    have he := data_ext pB h b.val hc
    rw [Submodule.projectionOnto_apply_left] at he
    exact hb he
  have leftOwned (hz : ellA = 0) : Cstar split = 1 := by
    have hn := nonzero_control.resolve_left (not_not.mpr hz)
    obtain ⟨i, hi⟩ := leftColumn hz
    apply le_antisymm
    · apply Finset.sup_le
      intro j _
      change rewriteCost ellA ellB (pA (e j)) (pB (e j)) ≤ 1
      simp only [rewriteCost, directionDemand, hz, ne_eq, not_true_eq_false,
        and_false, if_false, add_zero]
      split_ifs <;> omega
    · apply Finset.le_sup_of_le (Finset.mem_univ i)
      change 1 ≤ rewriteCost ellA ellB (pA (e i)) (pB (e i))
      simp [rewriteCost, directionDemand, hz, hn, hi]
  have rightOwned (hz : ellB = 0) : Cstar split = 1 := by
    have hn := nonzero_control.resolve_right (not_not.mpr hz)
    obtain ⟨i, hi⟩ := rightColumn hz
    apply le_antisymm
    · apply Finset.sup_le
      intro j _
      change rewriteCost ellA ellB (pA (e j)) (pB (e j)) ≤ 1
      simp only [rewriteCost, directionDemand, hz, ne_eq, not_true_eq_false,
        and_false, if_false, zero_add]
      split_ifs <;> omega
    · apply Finset.le_sup_of_le (Finset.mem_univ i)
      change 1 ≤ rewriteCost ellA ellB (pA (e i)) (pB (e i))
      simp [rewriteCost, directionDemand, hz, hn, hi]
  have distributed (hNA : ellA ≠ 0) (hNB : ellB ≠ 0) : Cstar split = 2 := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hNA
    obtain ⟨b, hb⟩ := DFunLike.ne_iff.mp hNB
    have ha1 : ellA a = 1 := (binary (ellA a)).resolve_left ha
    have hb1 : ellB b = 1 := (binary (ellB b)).resolve_left hb
    have mixed : ∃ i, ellA (pA (e i)) ≠ 0 := by
      by_contra h
      push Not at h
      have hc : ((a : Source d) + (b : Source d)).2 = 0 := by
        change ellA a + ellB b = 0
        rw [ha1, hb1]
        rfl
      have hz := data_ext (ellA.comp pA) h ((a : Source d) + (b : Source d)) hc
      have hp : pA ((a : Source d) + (b : Source d)) = a := by simp [pA]
      change ellA (pA ((a : Source d) + (b : Source d))) = 0 at hz
      rw [hp, ha1] at hz
      exact one_ne_zero hz
    obtain ⟨i, hi⟩ := mixed
    have hα : pA (e i) ≠ 0 := by intro h; apply hi; simp [h]
    have hβ : pB (e i) ≠ 0 := by
      intro h
      have hc := columns i
      rw [h, map_zero, add_zero] at hc
      exact hi hc
    apply le_antisymm maxBound
    apply Finset.le_sup_of_le (Finset.mem_univ i)
    change 2 ≤ rewriteCost ellA ellB (pA (e i)) (pB (e i))
    simp [rewriteCost, directionDemand, hα, hβ, hNA, hNB]
  have positive : ∃ i : Fin d, 0 < splitCost split i := by
    have hp : 0 < Cstar split := by
      by_cases hzeroA : ellA = 0
      · rw [leftOwned hzeroA]; decide
      · by_cases hzeroB : ellB = 0
        · rw [rightOwned hzeroB]; decide
        · rw [distributed hzeroA hzeroB]; decide
    by_contra h
    push Not at h
    have hz : Cstar split ≤ 0 := Finset.sup_le (fun i _ => h i)
    omega
  refine ⟨leftOwned, rightOwned, distributed, positive, ?_, ?_⟩
  · constructor
    · intro i
      let alpha := pA (e i)
      let beta := pB (e i)
      obtain ⟨_, _, _, hc, hat⟩ := rewrite_directional_sharpness.{0,0,0,0} ellA ellB alpha beta
      refine ⟨rewriteProtocol ellA ellB alpha beta, hc, ?_⟩
      intro a b n t ht
      obtain ⟨m, s, hs, _, _, hlen⟩ := hat a b
      -- Compare the two actual executions with the supplier instantiated at A and B.
      have he := (rewrite_directional_sharpness.{0,0,0,0} ellA ellB alpha beta).2.1
        (rewriteProtocol ellA ellB alpha beta) a b n m t s ht hs
      rw [he, hlen]
      change splitCost split i ≤ Cstar split
      exact Finset.le_sup (Finset.mem_univ i)
    · intro K hK
      apply Finset.sup_le
      intro i _
      obtain ⟨p, hc, hbudget⟩ := hK i
      obtain ⟨n, t, ht⟩ := hc.1 0 0
      exact ((rewrite_directional_sharpness.{0,0,0,0} ellA ellB (pA (e i)) (pB (e i))).2.2.1
        id id p hc 0 0 n t ht |>.2.2).trans (hbudget 0 0 n t ht)
  · intro MA MB Root C K hK
    have direction (i : Fin d) (a : A) (b : B) :
        directionDemand (pA (e i)) ellB ≤
          rightCount (C.trace (.rewrite i) (C.initial a b)) ∧
        directionDemand (pB (e i)) ellA ≤
          leftCount (C.trace (.rewrite i) (C.initial a b)) ∧
        splitCost split i ≤ C.cost (C.initial a b) (.rewrite i) := by
      let f : Action d := .rewrite i
      let root := C.rootA f (C.initA 0)
      have roots (a' : A) (b' : B) : C.rootA f (C.initA a') = root ∧
          C.rootB f (C.initB b') = root := by
        have hleft := C.root_agree _ (.initial a' 0) f
        have hzero := C.root_agree _ (.initial 0 0) f
        have hright := C.root_agree _ (.initial 0 b') f
        exact ⟨hleft.trans hzero.symm, hright.symm⟩
      let original := C.protocol f root
      let p : EndpointProtocol MA MB A B := {
        node := original.node
        outA := fun m t => C.readA (original.outA m t)
        outB := fun m t => C.readB (original.outB m t) }
      have sourceRewrite (a' : A) (b' : B) :
          f.apply ((a' : Source d) + (b' : Source d)) =
            (ellA a' + ellB b') • e i := by
        ext j <;> simp [f, Action.apply, controlRewrite, e, ellA, ellB,
          controlRestriction, Pi.single_apply, smul_eq_mul]
      have hc : RewriteCorrect ellA ellB (pA (e i)) (pB (e i)) C.initA C.initB p := by
        constructor
        · intro a' b'
          obtain ⟨t, n, hn⟩ := C.terminates _ (.initial a' b') f
          refine ⟨n, t, ?_⟩
          change execute answer (C.protocol f (C.rootA f (C.initA a'))).policy n []
            (C.initA a', C.initB b') = some (t, ()) at hn
          rw [(roots a' b').1] at hn
          exact hn
        · intro a' b' n t ht
          have hx : C.toControllerData.Exec f (C.initA a', C.initB b') t := by
            refine ⟨n, ?_⟩
            change execute answer (C.protocol f (C.rootA f (C.initA a'))).policy n []
              (C.initA a', C.initB b') = some (t, ())
            rw [(roots a' b').1]
            exact ht
          have hh := C.correct _ (.initial a' b') f t hx
          dsimp only at hh
          simp only [C.read_initA, C.read_initB] at hh
          change C.readA ((C.protocol f (C.rootA f (C.initA a'))).outA
              (C.initA a') (bits t)) = pA (f.apply ((a' : Source d) + (b' : Source d))) ∧
            C.readB ((C.protocol f (C.rootA f (C.initA a'))).outB
              (C.initB b') (bits t)) = pB (f.apply ((a' : Source d) + (b' : Source d))) at hh
          rw [(roots a' b').1, sourceRewrite a' b', map_smul, map_smul] at hh
          exact hh
      obtain ⟨n, hn⟩ := Classical.choose_spec (C.terminates
        (C.initial a b).val (C.initial a b).property f)
      have ht : execute answer p.policy n [] (C.initA a, C.initB b) =
          some (C.trace f (C.initial a b), ()) := by
        change execute answer (C.protocol f (C.rootA f (C.initA a))).policy n []
          (C.initA a, C.initB b) = some (C.trace f (C.initial a b), ()) at hn
        rw [(roots a b).1] at hn
        exact hn
      have lb := (rewrite_directional_sharpness.{0,0,u,v} ellA ellB (pA (e i))
        (pB (e i))).2.2.1 C.initA C.initB p hc a b n (C.trace f (C.initial a b)) ht
      simpa only [splitCost, Controller.cost, f] using lb
    constructor
    · apply Finset.sup_le
      intro i _
      have hh := hK 0 0 [.rewrite i]
      simp only [Comm, Nat.add_zero] at hh
      exact (direction i 0 0).2.2.trans hh
    · intro a b i
      exact ⟨(direction i a b).1, (direction i a b).2.1⟩

#print axioms fixed_split_rewrite_budget

end D5.S3.ObserverMemory.Algorithms.FixedSplitRewriteBudget
