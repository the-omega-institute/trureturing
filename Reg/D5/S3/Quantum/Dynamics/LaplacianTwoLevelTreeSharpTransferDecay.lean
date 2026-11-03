import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Sharp Root-to-Leaf Transfer Supremum and Tail Decay -/

namespace Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
open _root_.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
open _root_.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace PellSupremum

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (m : ℕ),
    approxTime (O.readout () () m) < approxTime (m + 1) ∧
      scaledTransferSet.Nonempty ∧ BddAbove scaledTransferSet ∧
      IsLUB scaledTransferSet optimalTransferConst ∧
      sSup scaledTransferSet = optimalTransferConst ∧
      (∀ (i₀ : Fin 2) (j₀ : Fin 1),
        (scaledTransferSet21 i₀ j₀).Nonempty ∧ BddAbove (scaledTransferSet21 i₀ j₀) ∧
          IsLUB (scaledTransferSet21 i₀ j₀) optimalTransferConst ∧
          sSup scaledTransferSet = sSup (scaledTransferSet21 i₀ j₀) ∧
          sSup (scaledTransferSet21 i₀ j₀) = optimalTransferConst) ∧
      (∀ (k l : ℕ), 2 ≤ k → 1 ≤ l → ∀ (i : Fin k) (j : Fin l) (t : ℝ),
        ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb k l i j t <
          optimalTransferConst) ∧
      Filter.Tendsto approxTime Filter.atTop Filter.atTop ∧
      (∀ (i₀ : Fin 2) (j₀ : Fin 1),
        Filter.Tendsto
          (fun j : ℕ => ((5 : ℝ) ^ ((3 : ℝ) / 2)) * leafTransferProb 2 1 i₀ j₀ (approxTime j))
          Filter.atTop (nhds optimalTransferConst))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact lt_irrefl (approxTime 2) (h 1).1

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@sharp_transfer_supremum_and_pell_approx)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_transfer_supremum_and_pell_approx, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@sharp_transfer_supremum_and_pell_approx)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ m => m) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay.PellSupremum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay.PellSupremum.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PellSupremum

namespace TailDecay

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig
    (fun _ _ N => max (envelopeG (tailThresholdD N)) (envelopeH (tailThresholdD N)))
    (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (N : ℝ) (_hN : 4 ≤ N),
    1 ≤ tailTransferSup N ∧ tailTransferSup N ≤ tailBoundingSup N ∧
      tailBoundingSup N ≤ O.readout () () N ∧
      (∀ M : ℝ,
        (tailBoundingSet M).Nonempty ∧ BddAbove (tailBoundingSet M) ∧
          IsLUB (tailBoundingSet M) (tailBoundingSup M) ∧
          (tailTransferSet M).Nonempty ∧ BddAbove (tailTransferSet M) ∧
          IsLUB (tailTransferSet M) (tailTransferSup M)) ∧
      Filter.Tendsto tailBoundingSup Filter.atTop (nhds (1 : ℝ)) ∧
      Filter.Tendsto tailTransferSup Filter.atTop (nhds (1 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℝ, ∀ (k l : ℕ), 2 ≤ k → 1 ≤ l → N₀ ≤ (treeOrder k l : ℝ) →
        ∀ (i : Fin k) (j : Fin l) (t : ℝ),
          leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 ∧
            (leafBoundingEntry k l i j) ^ 2 ≤
              (1 + ε) * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2))) ∧
      (∀ β : ℝ, (3 : ℝ) / 2 < β → ¬ ∃ C : ℝ, ∀ (k l : ℕ), 2 ≤ k → 1 ≤ l →
        ∀ (i : Fin k) (j : Fin l) (t : ℝ),
          leafTransferProb k l i j t ≤ C * ((treeOrder k l : ℝ) ^ (-β)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h4 := h 4 (by norm_num)
  have h1 : 1 ≤ tailTransferSup 4 := h4.1
  have h2 : tailTransferSup 4 ≤ tailBoundingSup 4 := h4.2.1
  have h3 : tailBoundingSup 4 ≤ 0 := h4.2.2.1
  linarith

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  refine ⟨(), 5, 17, ?_⟩
  change max (envelopeG (tailThresholdD 5)) (envelopeH (tailThresholdD 5)) ≠
    max (envelopeG (tailThresholdD 17)) (envelopeH (tailThresholdD 17))
  have ht5 : tailThresholdD 5 = Real.sqrt 5 := by
    have h4 : Real.sqrt ((5 : ℝ) - 1) = 2 := by
      rw [show (5 : ℝ) - 1 = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    unfold tailThresholdD; rw [h4, show (4 : ℝ) * 2 - 3 = 5 by norm_num, max_self]
  have ht17 : tailThresholdD 17 = Real.sqrt 13 := by
    have h16 : Real.sqrt ((17 : ℝ) - 1) = 4 := by
      rw [show (17 : ℝ) - 1 = (4 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    unfold tailThresholdD
    rw [h16, show (4 : ℝ) * 4 - 3 = 13 by norm_num,
      max_eq_right (Real.sqrt_le_sqrt (by norm_num))]
  rw [ht5, ht17]
  have h5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h5_lt : Real.sqrt 5 < Real.sqrt 13 :=
    (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr (by norm_num)
  have hanti := spectral_envelope_and_antitonicity (Real.sqrt 5) (Real.sqrt 13) h5_pos h5_lt
  exact ne_of_gt (max_lt (lt_of_lt_of_le hanti.2.2.2.1 (le_max_left _ _))
    (lt_of_lt_of_le hanti.2.2.2.2.1 (le_max_right _ _)))

def evidence : Registration arena
    (type_of% (@sharp_asymptotic_tail_decay)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_asymptotic_tail_decay, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@sharp_asymptotic_tail_decay)
      (type_of% (realize.{0,0,0,0,0} sig
        (fun _ _ N => max (envelopeG (tailThresholdD N)) (envelopeH (tailThresholdD N)))
        (fun e => nomatch e))) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay.TailDecay.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay.TailDecay.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig
    (fun _ _ N => max (envelopeG (tailThresholdD N)) (envelopeH (tailThresholdD N)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailDecay

end
end Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSharpTransferDecay
