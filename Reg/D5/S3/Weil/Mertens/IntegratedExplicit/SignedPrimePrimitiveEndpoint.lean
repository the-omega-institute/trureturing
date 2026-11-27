import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint
import Reg.Support.SingleDependentReadout

/-! Source readout of the zeta evaluation in the exact strip criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint
  (zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ ρ => riemannZeta ρ) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {β c : ℝ}, 1 / 2 < β → c ≠ 0 →
    ((∀ ρ : ℂ, V.readout () () ρ = 0 → ρ.re ≤ β) ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T in atTop,
        c * (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) ≤
          Real.exp ((β - 1 / 2) * T) * B)

private theorem zero_readout_fails : ¬ arena.Law zeroReadout := by
  intro h
  have hzeta (ρ : ℂ) (hρ : riemannZeta ρ = 0) : ρ.re ≤ 1 :=
    le_of_not_gt fun h => riemannZeta_ne_zero_of_one_lt_re h hρ
  have hbound :=
    (zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040
      (β := 1) (c := 1) (by norm_num) one_ne_zero).mp hzeta
  have hbad := (h (β := 1) (c := 1) (by norm_num) one_ne_zero).mpr hbound (2 : ℂ) rfl
  norm_num at hbad

private theorem actual_depends : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (2 : ℂ), (-2 : ℂ), ?_⟩
  change riemannZeta 2 ≠ riemannZeta (-2)
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  rw [hz]
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)

def family : Registration arena
    (type_of% @zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040,
    zeroReadout, zero_readout_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout zero_readout_fails
  dependence := actual_depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040)
    (Realization signature) Unit Unit where
  unitName := .str ``zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040 "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => riemannZeta ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveEndpoint
