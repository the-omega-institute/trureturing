import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the mixed-unitary pinching obstruction. -/

namespace Reg.D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation

open _root_.D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma)
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
open scoped BigOperators ComplexOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev TwoQubit := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

abbrev signature : Signature where
  Params := Unit
  State _ := TwoQubit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => ρ.trace) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def badWeights : Fin 4 → ℝ := ![1 / 2, 0, 0, 1 / 2]

private def badChannel (a : QubitMatrix) : QubitMatrix :=
  ∑ j : Fin 4, (badWeights j : ℂ) • (sigma j * a * star (sigma j))

private theorem badChannel_mixed : IsMixedUnitary badChannel := by
  refine ⟨4, badWeights, sigma, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [badWeights]
  · norm_num [badWeights, Fin.sum_univ_succ]
  · intro j
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose,
      (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma_properties j).1,
      (D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma_properties j).2]
  · intro a
    rfl

private theorem badChannel_x : badChannel (sigma 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [badChannel, badWeights, sigma, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.vecMul, dotProduct,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitX, qubitZ, Complex.I_sq]

private theorem badChannel_z : badChannel (sigma 3) = sigma 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [badChannel, badWeights, sigma, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.vecMul, dotProduct,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitX, qubitZ, Complex.I_sq]

private theorem badChannel_nonisotropic : ¬ IsIsotropic badChannel := by
  intro h
  obtain ⟨γ, hγ, u, hu, hbranch⟩ := h
  have htx : Matrix.trace (sigma 1) = 0 := by
    norm_num [sigma, Matrix.trace, Matrix.diag,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitX, qubitZ, Fin.sum_univ_succ]
  have htz : Matrix.trace (sigma 3) = 0 := by
    norm_num [sigma, Matrix.trace, Matrix.diag,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitX, qubitZ, Fin.sum_univ_succ]
  rcases hbranch with hbranch | hbranch
  · have hx := hbranch (sigma 1)
    have hz := hbranch (sigma 3)
    rw [badChannel_x, htx, zero_div, zero_smul] at hx
    have hcoef : ((1 - γ : ℝ) : ℂ) = 0 := by
      by_contra hc
      have hU : u * sigma 1 * star u ≠ 0 := by
        intro hU
        have hU' := congrArg (fun M : QubitMatrix => star u * M * u) hU
        have hleft : star u * u = (1 : QubitMatrix) :=
          Matrix.mem_unitaryGroup_iff'.mp hu
        have hright : u * star u = (1 : QubitMatrix) :=
          Matrix.mem_unitaryGroup_iff.mp hu
        have heq : star u * (u * sigma 1 * star u) * u =
            (star u * u) * sigma 1 * (star u * u) := by noncomm_ring
        rw [heq, hleft] at hU'
        have hs : sigma 1 = 0 := by simpa using hU'
        have he := congrArg (fun M : QubitMatrix => M 0 1) hs
        norm_num [sigma,
          D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
          qubitX] at he
      simp only [smul_zero, add_zero] at hx
      exact hc ((smul_eq_zero.mp hx.symm).resolve_right hU)
    have hreal : (1 - γ : ℝ) = 0 := by exact_mod_cast hcoef
    rw [badChannel_z, htz, zero_div, hreal] at hz
    have he := congrArg (fun M : QubitMatrix => M 0 0) hz
    norm_num [sigma,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitZ] at he
  · have hx := hbranch (sigma 1)
    have hz := hbranch (sigma 3)
    rw [badChannel_x, htx, zero_div, zero_smul] at hx
    have hcoef : ((1 - γ : ℝ) : ℂ) = 0 := by
      by_contra hc
      have hU : u * (sigma 1)ᵀ * star u ≠ 0 := by
        intro hU
        have hU' := congrArg (fun M : QubitMatrix => star u * M * u) hU
        have hleft : star u * u = (1 : QubitMatrix) :=
          Matrix.mem_unitaryGroup_iff'.mp hu
        have hright : u * star u = (1 : QubitMatrix) :=
          Matrix.mem_unitaryGroup_iff.mp hu
        have heq : star u * (u * (sigma 1)ᵀ * star u) * u =
            (star u * u) * (sigma 1)ᵀ * (star u * u) := by noncomm_ring
        rw [heq, hleft] at hU'
        have hs : (sigma 1)ᵀ = 0 := by simpa using hU'
        have he := congrArg (fun M : QubitMatrix => M 0 1) hs
        norm_num [sigma, Matrix.transpose,
          D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
          qubitX] at he
      simp only [smul_zero, add_zero] at hx
      exact hc ((smul_eq_zero.mp hx.symm).resolve_right hU)
    have hreal : (1 - γ : ℝ) = 0 := by exact_mod_cast hcoef
    rw [badChannel_z, htz, zero_div, hreal] at hz
    have he := congrArg (fun M : QubitMatrix => M 0 0) hz
    norm_num [sigma, Matrix.transpose,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitZ] at he

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (φ : QubitMatrix → QubitMatrix) (_hφ : IsMixedUnitary φ)
    (_hi : ¬ IsIsotropic φ),
    ∃ ρ : TwoQubit,
      ρ.PosSemidef ∧ R.readout () () ρ = 1 ∧
      IsNondegenerate (partialTraceRight ρ) ∧
      IsNondegenerate (φ (partialTraceRight ρ)) ∧
      pinchA (localMap φ ρ) ≠ localMap φ (pinchA ρ)

private theorem bridge : (type_of% @result) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h badChannel badChannel_mixed badChannel_nonisotropic
  obtain ⟨ρ, _, htrace, _, _, _⟩ := hh
  simp [rejected, realize] at htrace

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : TwoQubit), (1 : TwoQubit), ?_⟩
  norm_num [actual, realize, Matrix.trace]

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => ρ.trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
