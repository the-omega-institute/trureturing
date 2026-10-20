import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CfmEndpointPositivity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.CfmRadialDerivative
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Matrix.CfmRadialDerivative
open _root_.D5.S3.Quantum.Matrix.RadialConvexity
open _root_.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ ε => ε) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1/20000 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (ε : ℝ), EndpointPositive n (R.readout () () ε) →
    ∀ {A C B : Mat n}, A ∈ cayleyDomain n → C ∈ cayleyDomain n → B ∈ cayleyDomain n →
      A ≤ C → C ≤ B →
      frobeniusNorm (resolventSum ε C - resolventSum ε A) ≤
          frobeniusNorm (resolventSum ε B - resolventSum ε A) ∧
        frobeniusNorm (resolventSum ε B - resolventSum ε C) ≤
          frobeniusNorm (resolventSum ε B - resolventSum ε A)
abbrev sourceScope := type_of% (@radial_of_endpoint_positive)

private theorem bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem scalar_resolvent (s x : ℝ) (hs : s - x ≠ 0) :
    CayleyResolvent.resolvent s (x • (1 : Mat 3)) = (s - x)⁻¹ • (1 : Mat 3) := by
  unfold CayleyResolvent.resolvent
  have he : s • (1 : Mat 3) - x • 1 = (s - x) • 1 := by module
  rw [he]
  apply Matrix.inv_eq_right_inv
  simp [smul_mul_smul, hs]

private theorem scalar_sum (x : ℝ) (h₂ : 2-x ≠ 0) (h₃ : 3-x ≠ 0) (h₄ : 4-x ≠ 0) :
    resolventSum 6 (x • (1 : Mat 3)) =
      ((2-x)⁻¹ + (3-x)⁻¹ - 6 * (4-x)⁻¹) • (1 : Mat 3) := by
  simp only [resolventSum, scalar_resolvent 2 x h₂, scalar_resolvent 3 x h₃,
    scalar_resolvent 4 x h₄, smul_smul]
  module

private theorem scalar_domain (x : ℝ) (hl : -1 < x) (hr : x < 1) :
    x • (1 : Mat 3) ∈ cayleyDomain 3 := by
  constructor
  · have h : ((1+x) • (1 : Mat 3)).PosDef :=
      Matrix.PosDef.one.smul (by linarith : 0 < 1+x)
    convert h using 1 <;> module
  · have h : ((1-x) • (1 : Mat 3)).PosDef :=
      Matrix.PosDef.one.smul (by linarith : 0 < 1-x)
    convert h using 1 <;> module

private theorem six_fails_radial : ¬
    (∀ {A C B : Mat 3}, A ∈ cayleyDomain 3 → C ∈ cayleyDomain 3 → B ∈ cayleyDomain 3 →
      A ≤ C → C ≤ B →
      frobeniusNorm (resolventSum 6 C - resolventSum 6 A) ≤
          frobeniusNorm (resolventSum 6 B - resolventSum 6 A) ∧
        frobeniusNorm (resolventSum 6 B - resolventSum 6 C) ≤
          frobeniusNorm (resolventSum 6 B - resolventSum 6 A)) := by
  intro h
  let A : Mat 3 := (-1/2 : ℝ) • 1
  let C : Mat 3 := (0 : ℝ) • 1
  let B : Mat 3 := (1/2 : ℝ) • 1
  have hA := scalar_domain (-1/2) (by norm_num) (by norm_num)
  have hC := scalar_domain 0 (by norm_num) (by norm_num)
  have hB := scalar_domain (1/2) (by norm_num) (by norm_num)
  have hAC : A ≤ C := by
    apply sub_nonneg.mp
    have h : ((1/2 : ℝ) • (1 : Mat 3)).PosSemidef :=
      Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1/2)
    convert h.nonneg using 1 <;> dsimp [A, C] <;> module
  have hCB : C ≤ B := by
    apply sub_nonneg.mp
    have h : ((1/2 : ℝ) • (1 : Mat 3)).PosSemidef :=
      Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1/2)
    convert h.nonneg using 1 <;> dsimp [C, B] <;> module
  have hgA : resolventSum 6 A = (-68/105 : ℝ) • (1 : Mat 3) := by
    rw [scalar_sum (-1/2) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hgB : resolventSum 6 B = (-68/105 : ℝ) • (1 : Mat 3) := by
    rw [scalar_sum (1/2) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hgC : resolventSum 6 C = (-2/3 : ℝ) • (1 : Mat 3) := by
    rw [scalar_sum 0 (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hi := (h hA hC hB hAC hCB).1
  rw [hgA, hgB, sub_self] at hi
  simp only [frobeniusNorm, map_zero, norm_zero] at hi
  have hz : resolventSum 6 C - (-68/105 : ℝ) • (1 : Mat 3) = 0 := by
    apply (vectorize 3).injective
    simpa [C] using norm_le_zero_iff.mp hi
  have he := congrArg (fun M : Mat 3 => M 0 0) hz
  norm_num [hgC, Matrix.sub_apply] at he

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood : EndpointPositive 3 (1/20000 : ℝ) :=
    fun U hU V hV hUV => CfmEndpointPositivity.endpoint_derivatives_positive U V hU hV hUV
  exact six_fails_radial (h 6 hgood)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@radial_of_endpoint_positive), rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_of_endpoint_positive) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CfmRadialDerivative.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CfmRadialDerivative.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ε => ε) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmRadialDerivative
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Quantum.Matrix.CfmRadialDerivative
