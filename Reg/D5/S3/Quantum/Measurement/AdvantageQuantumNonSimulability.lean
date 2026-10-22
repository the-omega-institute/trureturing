import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
import Reg.Support.DependentFamily

/-! Least-eigenvalue readouts of binary advantage-quantum measurements. -/

namespace Reg.D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability

open _root_.D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
open _root_.D5.S3.Resource.CompositeCones (posSemidef_blockPositive)
open _root_.D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation (IsPOVM)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The measurement includes its Hermitian and block-positive effect certificates. -/
abbrev signature : Signature where
  Params := Σ _dA : ℕ, ℕ
  State p := {E : Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ // IsDovm E}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 2 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M i => aqLeastEigenvalue (M.property i).1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -2) (fun e => nomatch e)

/-- Keep both spectral inequalities and the full finite-copy nonsimulability assertion. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ dA dB : ℕ, 1 ≤ dA → 1 ≤ dB →
    ∀ E : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ, ∀ hE : IsDovm E,
      (∃ i, R.readout () ⟨dA, dB⟩ ⟨E, hE⟩ i < 0 ∧
        1 + R.readout () ⟨dA, dB⟩ ⟨E, hE⟩ i < aqGreatestEigenvalue (hE i).1 ∧
        aqGreatestEigenvalue (hE i).1 < 1) →
      ∀ n : ℕ, ¬ QuantumSimulable E n

private theorem zero_dovm (dA dB : ℕ) :
    IsDovm (0 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) := by
  intro i
  fin_cases i
  · exact ⟨isHermitian_zero, posSemidef_blockPositive PosSemidef.zero⟩
  · simpa [binaryEffect] using
      (And.intro (isHermitian_one :
        (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ).IsHermitian)
        (posSemidef_blockPositive
        (PosSemidef.one : (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ).PosSemidef)))

private theorem one_dovm (dA dB : ℕ) :
    IsDovm (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) := by
  intro i
  fin_cases i
  · exact ⟨isHermitian_one, posSemidef_blockPositive PosSemidef.one⟩
  · simpa [binaryEffect] using
      (And.intro (isHermitian_zero :
        (0 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ).IsHermitian)
        (posSemidef_blockPositive
        (PosSemidef.zero : (0 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ).PosSemidef)))

private theorem singleton_eigenvalues
    {A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ} (hA : A.IsHermitian) :
    hA.eigenvalues = fun _ => (trace A).re := by
  funext i
  have ht : (trace A).re = ∑ j, hA.eigenvalues j := by
    change RCLike.re (trace A) = _
    rw [hA.trace_eq_sum_eigenvalues, map_sum]
    simp only [RCLike.ofReal_re]
  exact (ht.trans (Fintype.sum_subsingleton _ i)).symm

private theorem singleton_least
    {A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ} (hA : A.IsHermitian) :
    aqLeastEigenvalue hA = (trace A).re := by
  rw [aqLeastEigenvalue, singleton_eigenvalues]
  simp

private theorem singleton_greatest
    {A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ} (hA : A.IsHermitian) :
    aqGreatestEigenvalue hA = (trace A).re := by
  rw [aqGreatestEigenvalue, singleton_eigenvalues]
  simp

private theorem zero_simulable :
    QuantumSimulable (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) 0 := by
  refine ⟨![0, 1], ⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact PosSemidef.zero
    · exact PosSemidef.one
  · simp [Fin.sum_univ_two]
  · intro ρ hρ i
    fin_cases i
    · simp [binaryEffect]
    · change (trace (copyState 0 ρ * 1)).re = (trace (ρ * (1 - 0))).re
      simp only [sub_zero, mul_one, hρ.2.1, Complex.one_re]
      simp [copyState, Matrix.trace, Matrix.diag]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmax : aqGreatestEigenvalue ((zero_dovm 1 1) 0).1 = 0 := by
    rw [singleton_greatest]
    simp [binaryEffect]
  have hbad := h 1 1 le_rfl le_rfl 0 (zero_dovm 1 1)
    ⟨0, by norm_num [rejected, realize], by norm_num [rejected, realize, hmax],
      by norm_num [hmax]⟩ 0
  exact hbad zero_simulable

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, ⟨0, zero_dovm 1 1⟩, ⟨1, one_dovm 1 1⟩, ?_⟩
  intro h
  have he := congrFun h 0
  change aqLeastEigenvalue ((zero_dovm 1 1) 0).1 =
    aqLeastEigenvalue ((one_dovm 1 1) 0).1 at he
  rw [singleton_least, singleton_least] at he
  norm_num [binaryEffect, Matrix.trace, Matrix.diag] at he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ M i => aqLeastEigenvalue (M.property i).1)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
    definition := some {
      owner := `D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
      name := `D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain",
        "arg", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
