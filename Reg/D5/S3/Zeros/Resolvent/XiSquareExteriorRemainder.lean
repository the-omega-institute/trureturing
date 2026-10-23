import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open _root_.D5.S3.Weil.ZeroSum
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open LeanInformationAudit Complex

noncomputable section
namespace Reg.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder

abbrev remainderSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ZeroData, Σ _ : Finset ℕ, ℂ) (fun _ => ℂ) (fun _ => ℝ)

def remainderActual : Realization remainderSignature :=
  realize remainderSignature (fun _ p w =>
    ‖exteriorSource p.1 p.2.1 (p.2.2 + w) / exteriorSource p.1 p.2.1 p.2.2 *
      Complex.exp (-w * logDeriv (exteriorSource p.1 p.2.1) p.2.2) - 1‖)
    (fun e => nomatch e)

def remainderRejected : Realization remainderSignature :=
  realize remainderSignature (fun _ _ _ => 1) (fun e => nomatch e)

def remainderArena : Arena where
  signature := remainderSignature
  Law R := ∀ (Z : ZeroData) (s : Finset ℕ) (a : ℂ)
      (_ha : exteriorSource Z s a ≠ 0),
    (∀ i : ℕ, analyticOrderNatAt xiSquareSource ((Z.gamma i) ^ 2) = Z.multiplicity i) ∧
    (∀ z : ℂ, xiSquareSource z = clusterSource Z s z * exteriorSource Z s z) ∧
    Differentiable ℂ (exteriorSource Z s) ∧
    Differentiable ℂ (fun w : ℂ =>
      exteriorSource Z s (a + w) / exteriorSource Z s a *
        Complex.exp (-w * logDeriv (exteriorSource Z s) a)) ∧
    ∀ w : ℂ, R.readout () ⟨Z, s, a⟩ w ≤
      (Real.exp (1 / 2) - 1) * ‖w‖ ^ 2 * exteriorSquareMass Z s a *
        Real.exp (‖w‖ ^ 2 * exteriorSquareMass Z s a / 2)

private theorem exterior_zero_value (Z : ZeroData) : exteriorSource Z ∅ 0 = 1 := by
  change (∏' k : (Σ i : ℕ, Fin (Z.multiplicity i)),
    (1 - (0 : ℂ) * (if k.1 ∈ (∅ : Finset ℕ) then 0 else
      if 0 < (Z.gamma k.1).re then ((Z.gamma k.1) ^ 2)⁻¹ else 0))) = 1
  simp

private theorem remainder_rejected : ¬ remainderArena.Law remainderRejected := by
  intro h
  have hA : exteriorSource zetaZeroData ∅ 0 ≠ 0 := by
    rw [exterior_zero_value]
    exact one_ne_zero
  have hh := (h zetaZeroData ∅ 0 hA).2.2.2.2 (0 : ℂ)
  change (1 : ℝ) ≤ _ at hh
  norm_num at hh

private theorem remainder_dependence :
    ObservationalDependence remainderSignature remainderActual := by
  intro role
  let Z := zetaZeroData
  have hreal : (Z.gamma 0).re ≠ 0 := by
    have h := _root_.D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.ZeroData.im_ne_zero
      Z 0 (Z.zero_isNontrivial 0)
    have heq : (Z.gamma 0).re = (Z.zero 0).im := by
      simp [ZeroData.gamma, spectralParameter,
        _root_.D5.S3.Weil.Convention.criticalAbscissa]
    rwa [heq]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, 0 < (Z.gamma i).re := by
    by_cases hp : 0 < (Z.gamma 0).re
    · exact ⟨0, hp⟩
    · refine ⟨Z.reflection 0, ?_⟩
      rw [Z.gamma_reflection, Complex.neg_re]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hreal)
  have hgamma : (Z.gamma i) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.zero_re] at hr
    linarith
  have hroot : exteriorSource Z ∅ ((Z.gamma i) ^ 2) = 0 := by
    change (∏' k : (Σ j : ℕ, Fin (Z.multiplicity j)),
      (1 - (Z.gamma i) ^ 2 * (if k.1 ∈ (∅ : Finset ℕ) then 0 else
        if 0 < (Z.gamma k.1).re then ((Z.gamma k.1) ^ 2)⁻¹ else 0))) = 0
    apply tprod_of_exists_eq_zero
    refine ⟨⟨i, ⟨0, Z.multiplicity_pos i⟩⟩, ?_⟩
    simp [hi, mul_inv_cancel₀ hgamma]
  refine ⟨⟨Z, ∅, 0⟩, 0, (Z.gamma i) ^ 2, ?_⟩
  change
    ‖exteriorSource Z ∅ (0 + 0) / exteriorSource Z ∅ 0 *
      Complex.exp (-(0 : ℂ) * logDeriv (exteriorSource Z ∅) 0) - 1‖ ≠
    ‖exteriorSource Z ∅ (0 + (Z.gamma i) ^ 2) / exteriorSource Z ∅ 0 *
      Complex.exp (-(Z.gamma i) ^ 2 * logDeriv (exteriorSource Z ∅) 0) - 1‖
  simp [exterior_zero_value, hroot]

def remainderEvidence : Registration remainderArena
    (type_of%
      (@_root_.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder.xi_square_cluster_exterior_remainder)) where
  actual := remainderActual
  bridge := Iff.rfl
  variation := ⟨xi_square_cluster_exterior_remainder, remainderRejected, remainder_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    remainderArena.Law remainderActual remainderRejected remainder_rejected
  dependence := remainder_dependence

noncomputable def remainderRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder.xi_square_cluster_exterior_remainder)
    (type_of% (realize remainderSignature (fun _ p w =>
      ‖exteriorSource p.1 p.2.1 (p.2.2 + w) / exteriorSource p.1 p.2.1 p.2.2 *
        Complex.exp (-w * logDeriv (exteriorSource p.1 p.2.1) p.2.2) - 1‖)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder.remainder_unit
  realizationName := `Reg.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder.remainderEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨remainderArena⟩
  objectArena := .source ⟨remainderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source remainderArena ⟨remainderEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize remainderSignature (fun _ p w =>
    ‖exteriorSource p.1 p.2.1 (p.2.2 + w) / exteriorSource p.1 p.2.1 p.2.2 *
      Complex.exp (-w * logDeriv (exteriorSource p.1 p.2.1) p.2.2) - 1‖)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms remainderEvidence
#print axioms remainderRegistration

end Reg.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
