/- GID: D5/S3/ConceptDynamics/Information/EqualEntropyTargetValueContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/EqualEntropyTargetValueContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal concept entropy and compression can coexist with opposite target sufficiency. -/

import D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
import D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity

/- Library-search audit trail (2026-08-25):
   * Exact repository hits `Concept`, `Refines`, `conceptLaw`,
     `readoutTargetLaw`, and `targetResidualEntropy` provide the canonical
     finite readout, factorization, pushforward-law, and conditional-target
     entropy primitives; all are imported rather than redeclared.
   * Repository body-shape searches for compression rates found no canonical
     declaration. The public statement therefore exposes the source model's
     attained-label counts and output-to-input cardinality ratios directly.
   * Repository and pinned-Mathlib searches found no theorem packaging the
     fixed two-coordinate witness. Exact hits `Fintype.sum_bool` and
     `Bool.false_ne_true` are applied in the direct computation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.EqualEntropyTargetValueContrast

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy

/-- On the uniform two-bit state space, the two coordinate readouts have the
same entropy, attained-label count, and compression ratio. Nevertheless, the
first readout completely determines the first-coordinate target, while the
second leaves one bit of target entropy and does not determine that target. -/
theorem equal_entropy_target_value_contrast :
    let mass : Bool × Bool -> Real := fun _ => 1 / 4
    let firstReadout : Concept (Bool × Bool) Bool := Prod.fst
    let secondReadout : Concept (Bool × Bool) Bool := Prod.snd
    let target : Concept (Bool × Bool) Bool := Prod.fst
    shannonEntropy (conceptLaw mass firstReadout) = Real.log 2 ∧
      shannonEntropy (conceptLaw mass secondReadout) = Real.log 2 ∧
      (Set.range firstReadout).ncard = 2 ∧
      (Set.range secondReadout).ncard = 2 ∧
      ((Set.range firstReadout).ncard : Real) /
          Fintype.card (Bool × Bool) = 1 / 2 ∧
      ((Set.range secondReadout).ncard : Real) /
          Fintype.card (Bool × Bool) = 1 / 2 ∧
      targetResidualEntropy mass firstReadout target = 0 ∧
      targetResidualEntropy mass secondReadout target = Real.log 2 ∧
      Refines target firstReadout ∧
      ¬Refines target secondReadout := by
  dsimp only
  have hhalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  have hfirstEntropy :
      shannonEntropy
          (conceptLaw (fun _ : Bool × Bool => (1 / 4 : Real)) Prod.fst) =
        Real.log 2 := by
    norm_num [conceptLaw, shannonEntropy, pushforward, Real.negMulLog,
      Fintype.sum_prod_type, Fintype.sum_bool, hhalf]
    ; ring
  have hsecondEntropy :
      shannonEntropy
          (conceptLaw (fun _ : Bool × Bool => (1 / 4 : Real)) Prod.snd) =
        Real.log 2 := by
    norm_num [conceptLaw, shannonEntropy, pushforward, Real.negMulLog,
      Fintype.sum_prod_type, Fintype.sum_bool, hhalf]
    ; ring
  have hfirstRange :
      Set.range (Prod.fst : Bool × Bool -> Bool) = Set.univ := by
    ext value
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(value, false), rfl⟩
  have hsecondRange :
      Set.range (Prod.snd : Bool × Bool -> Bool) = Set.univ := by
    ext value
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(false, value), rfl⟩
  have hfirstLabels :
      (Set.range (Prod.fst : Bool × Bool -> Bool)).ncard = 2 := by
    rw [hfirstRange, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_bool]
  have hsecondLabels :
      (Set.range (Prod.snd : Bool × Bool -> Bool)).ncard = 2 := by
    rw [hsecondRange, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_bool]
  have hfirstResidual :
      targetResidualEntropy (fun _ : Bool × Bool => (1 / 4 : Real))
          Prod.fst Prod.fst = 0 := by
    norm_num [targetResidualEntropy, readoutTargetLaw, conditionalEntropy,
      marginal, conditional, shannonEntropy, pushforward, Real.negMulLog,
      Fintype.sum_prod_type, Fintype.sum_bool]
  have hsecondResidual :
      targetResidualEntropy (fun _ : Bool × Bool => (1 / 4 : Real))
          Prod.snd Prod.fst = Real.log 2 := by
    norm_num [targetResidualEntropy, readoutTargetLaw, conditionalEntropy,
      marginal, conditional, shannonEntropy, pushforward, Real.negMulLog,
      Fintype.sum_prod_type, Fintype.sum_bool, hhalf]
    ; ring
  refine ⟨hfirstEntropy, hsecondEntropy, hfirstLabels, hsecondLabels, ?_, ?_,
    hfirstResidual, hsecondResidual, ⟨id, rfl⟩, ?_⟩
  · norm_num [hfirstLabels]
  · norm_num [hsecondLabels]
  · rintro ⟨factor, factorization⟩
    have collapsed :
        (Prod.fst : Bool × Bool -> Bool) (false, false) =
          Prod.fst (true, false) := by
      rw [factorization]
      rfl
    exact Bool.false_ne_true collapsed

#print axioms equal_entropy_target_value_contrast

end D5.S3.ConceptDynamics.Information.EqualEntropyTargetValueContrast
