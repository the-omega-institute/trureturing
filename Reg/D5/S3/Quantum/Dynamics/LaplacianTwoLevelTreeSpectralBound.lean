import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Two-Level Tree Spectral Transfer Bounds -/

namespace Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
open _root_.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
open _root_.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace LeafDynamics

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (k l : ℕ) (_hk : 2 ≤ k) (_hl : 1 ≤ l)
    (i i' : Fin k) (j j' : Fin l) (t : ℝ),
      (twoLevelTree k l).IsTree ∧
        (∃ φ : twoLevelTree k l ≃g twoLevelTree k l,
          φ (rootVertex k l) = rootVertex k l ∧
            φ (leafVertex k l i j) = leafVertex k l i' j') ∧
        leafTransferProb k l i j t = leafTransferProb k l i' j' t ∧
        leafBoundingEntry k l i j = leafBoundingEntry k l i' j' ∧
        lapPropagator (twoLevelTree k l) t (leafVertex k l i j) (rootVertex k l) =
          (1 : ℂ) / (treeOrder k l : ℂ) -
            Complex.exp (Complex.I * (specA k l : ℂ) * (t : ℂ)) /
              ((specA k l : ℂ) * (specD k l : ℂ)) +
            Complex.exp (Complex.I * (specB k l : ℂ) * (t : ℂ)) /
              ((specB k l : ℂ) * (specD k l : ℂ)) ∧
        leafBoundingEntry k l i j = 2 / (specA (O.readout () () k) l * specD k l) ∧
        leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hact := (twoLevelTree_leaf_dynamics_and_invariance 2 1 le_rfl le_rfl 0 0 0 0 0).2.2.2.2.2.1
  have hbad := (h 2 1 le_rfl le_rfl 0 0 0 0 0).2.2.2.2.2.1
  change leafBoundingEntry 2 1 0 0 = 2 / (specA 0 1 * specD 2 1) at hbad
  rw [hact] at hbad
  have hd_pos : 0 < specD 2 1 := by unfold specD; positivity
  have ha2_pos : 0 < specA 2 1 :=
    lt_trans zero_lt_one (sharp_global_spectral_transfer_bound 2 1 le_rfl le_rfl 0 0 0).2.1
  have h5_0 : (((0 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) ^ 2 + 4 * ((1 : ℕ) : ℝ) = 5 := by norm_num
  have h5_2 : (((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) ^ 2 + 4 * ((1 : ℕ) : ℝ) = 5 := by norm_num
  have ha0 : specA 0 1 = (3 - Real.sqrt 5) / 2 := by
    unfold specA specS specD; rw [h5_0]; push_cast; ring
  have ha2 : specA 2 1 = (5 - Real.sqrt 5) / 2 := by
    unfold specA specS specD; rw [h5_2]; push_cast; ring
  have ha0_pos : 0 < specA 0 1 := by
    rw [ha0]
    have hlt3 : Real.sqrt 5 < 3 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg 5) (by norm_num)).mp
        (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
    linarith
  have hdiff : specA 2 1 - specA 0 1 = 1 := by rw [ha2, ha0]; ring
  have hmul_eq : 2 * (specA 0 1 * specD 2 1) = 2 * (specA 2 1 * specD 2 1) :=
    (div_eq_div_iff (mul_ne_zero ha2_pos.ne' hd_pos.ne')
      (mul_ne_zero ha0_pos.ne' hd_pos.ne')).mp hbad
  have hzero : (specA 2 1 - specA 0 1) * (2 * specD 2 1) = 0 := by linarith
  rw [hdiff, one_mul] at hzero
  linarith

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@twoLevelTree_leaf_dynamics_and_invariance)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨twoLevelTree_leaf_dynamics_and_invariance, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@twoLevelTree_leaf_dynamics_and_invariance)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)))
      Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound.LeafDynamics.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound.LeafDynamics.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LeafDynamics

namespace EnvelopeAntitonicity

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ d => envelopeH d) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd₂ : d₁ < d₂),
    envelopeG d₁ ^ 2 = 16 * (1 / d₁ + 3 / d₁ ^ 2 + 3 / d₁ ^ 3 + 1 / d₁ ^ 4) ∧
      envelopeH d₁ ^ 2 =
        1 + 8 / d₁ + 38 / d₁ ^ 2 + 40 / d₁ ^ 3 + 25 / d₁ ^ 4 +
          64 / (d₁ * (d₁ ^ 2 - 2 * d₁ + 5)) ∧
      1 < O.readout () () d₁ ∧ envelopeG d₂ < envelopeG d₁ ∧ envelopeH d₂ < envelopeH d₁ ∧
      (∀ a : ℝ, 1 ≤ a → a ≤ upperFeasibleA d₁ →
        4 * ((a + d₁) ^ ((3 : ℝ) / 2)) / (Real.sqrt a * d₁ ^ 2) ≤
          max (envelopeG d₁) (envelopeH d₁))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 2 zero_lt_one one_lt_two).2.2.1
  change (1 : ℝ) < 0 at hbad
  linarith

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 1, 2,
    ne_of_gt (spectral_envelope_and_antitonicity 1 2 zero_lt_one one_lt_two).2.2.2.2.1⟩

def evidence : Registration arena
    (type_of% (@spectral_envelope_and_antitonicity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_envelope_and_antitonicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@spectral_envelope_and_antitonicity)
      (type_of%
        (realize.{0,0,0,0,0} sig (fun _ _ d => envelopeH d) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound.EnvelopeAntitonicity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound.EnvelopeAntitonicity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ d => envelopeH d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EnvelopeAntitonicity

namespace SharpGlobalBound

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (k l : ℕ) (_hk : 2 ≤ k) (_hl : 1 ≤ l)
    (i : Fin k) (j : Fin l) (t : ℝ),
      Real.sqrt 5 ≤ specD k l ∧ 1 < specA k l ∧ specA k l ≤ upperFeasibleA (specD k l) ∧
        (treeOrder k l : ℝ) = specA k l * (specA k l + specD k l) ∧
        ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ≤
          max (envelopeG (specD k l)) (envelopeH (specD k l)) ∧
        leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 ∧
        (leafBoundingEntry k l i j) ^ 2 ≤
          optimalTransferConst * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) ∧
        (((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 =
          optimalTransferConst ↔ O.readout () () k = 2 ∧ l = 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have heq := (sharp_global_spectral_transfer_bound 2 1 le_rfl le_rfl 0 0 0).2.2.2.2.2.2.2.mpr
    ⟨rfl, rfl⟩
  have hbad := ((h 2 1 le_rfl le_rfl 0 0 0).2.2.2.2.2.2.2.mp heq).1
  change (3 : ℕ) = 2 at hbad
  omega

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@sharp_global_spectral_transfer_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_global_spectral_transfer_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@sharp_global_spectral_transfer_bound)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound.SharpGlobalBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound.SharpGlobalBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SharpGlobalBound

end
end Reg.D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
