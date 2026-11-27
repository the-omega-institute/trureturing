import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed

/-! Source-bound readouts for the mixed derivative and the two trace identities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed

namespace MixedDerivative

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

private def coefficient (u a b : ℝ) : ℝ :=
  -b * (9 * a / 4) * (1 + u) / (1 - u) *
    (2 * (1 - 2 * _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.alpha (1 / u)) +
      2 * (1 - u) ^ 2 / (1 + u + u ^ 2))

private def actual : Realization signature :=
  realize signature (fun _ ua b => coefficient ua.1 ua.2 b) (fun e => nomatch e)

private def shifted : Realization signature :=
  realize signature (fun _ ua b => coefficient ua.1 ua.2 b + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u a b : ℝ), 0 < u → u < 1 → 0 < b → a = u ^ 3 * b → b * (1 + u ^ 3) = 1 →
    HasDerivAt (fun y => deriv (fun z =>
      deficit u a b (_root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.alpha (1 / u)) z y) 0)
      (R.readout () ⟨u, a⟩ b) 0

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hActual := hot_inner_mixed (1 / 2) (1 / 9) (8 / 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hShifted := h (1 / 2) (1 / 9) (8 / 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := hActual.unique hShifted
  change coefficient (1 / 2) (1 / 9) (8 / 9) =
    coefficient (1 / 2) (1 / 9) (8 / 9) + 1 at he
  linarith only [he]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  intro h
  change coefficient 0 1 0 = coefficient 0 1 1 at h
  norm_num [coefficient, _root_.D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic.alpha,
    Real.log_zero] at h

def family : Registration arena (type_of% @hot_inner_mixed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hot_inner_mixed, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hot_inner_mixed) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed.hot_inner_mixed.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed.MixedDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MixedDerivative

private abbrev equalitySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def equality : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def neverEqual : Realization equalitySignature :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equality_dependence : ObservationalDependence equalitySignature equality := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

namespace SpectralTrace

private abbrev arena : Arena where
  signature := equalitySignature
  Law R := ∀ (u a b k y : ℝ), 0 ≤ u →
    R.readout () ()
      ((embedded u a b k y ^ 3 * cfc Real.log (embedded u a b k y ^ 3)).trace.re)
      (spectral u a b (k ^ 2) y)

private theorem neverEqual_fails : ¬ arena.Law neverEqual := by
  intro h
  exact h 0 0 0 0 0 le_rfl

def family : Registration arena (type_of% @embedded_spectral) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨@embedded_spectral, neverEqual, neverEqual_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equality neverEqual neverEqual_fails
  dependence := equality_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@embedded_spectral) (Realization equalitySignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed.embedded_spectral.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed.SpectralTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralTrace

namespace DeficitTrace

private abbrev arena : Arena where
  signature := equalitySignature
  Law R := ∀ (u a b alpha k y : ℝ), 0 ≤ u →
    R.readout () () (deficit u a b alpha (k ^ 2) y)
      (b * ((9 / 8) * ((embedded u a b k y ^ 2 * embeddedGenerator u a b k y).trace).re -
        alpha * ((embedded u a b k y ^ 3 * cfc Real.log (embedded u a b k y ^ 3)).trace.re -
          ((embedded u a b k y ^ 3).trace.re * Real.log (embedded u a b k y ^ 3).trace.re +
            ((embedded u a b k y ^ 3) 0 0).re * Real.log a +
            ((embedded u a b k y ^ 3) 1 1).re * Real.log b))))

private theorem neverEqual_fails : ¬ arena.Law neverEqual := by
  intro h
  exact h 0 0 0 0 0 0 le_rfl

def family : Registration arena (type_of% @embedded_deficit) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨@embedded_deficit, neverEqual, neverEqual_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equality neverEqual neverEqual_fails
  dependence := equality_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@embedded_deficit) (Realization equalitySignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed.embedded_deficit.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed.DeficitTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeficitTrace

end Reg.D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
