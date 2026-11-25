import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower
import Reg.Support.SingleDependentReadout

/-! Observe the zero and window data jointly in each power law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Real
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_real_parts_nonempty)
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower

private abbrev signature (A : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => Prop × A)

private theorem dependence {A : Type} (data : ℂ → A) :
    ObservationalDependence (signature A)
      (realize (signature A) (fun _ _ z => (IsNontrivialZero z, data z)) (fun e => nomatch e)) := by
  intro i
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := zero_real_parts_nonempty
  refine ⟨(), z, 1, fun h => ?_⟩
  have hzero : IsNontrivialZero 1 := (congrArg Prod.fst h).mp hz
  exact (lt_irrefl (1 : ℝ)) (by simpa using hzero.2.2)

private def testZero : ℂ := (3 / 4 : ℝ)

private theorem testZero_re : testZero.re = 3 / 4 := Complex.ofReal_re _

private theorem test_strip (z : ℂ) (hz : z = testZero) : z.re ≤ 1 - 1 / 4 := by
  rw [hz, testZero_re]
  norm_num

namespace FixedPower

private def actual : Realization (signature (ℝ → ℝ → ℝ)) :=
  realize _ (fun _ _ z => (IsNontrivialZero z, weightedNegativeMass psiErrorKernel))
    (fun e => nomatch e)

private def rejected : Realization (signature (ℝ → ℝ → ℝ)) :=
  realize _ (fun _ _ z => (z = testZero, fun _ _ => 0)) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature (ℝ → ℝ → ℝ)
  Law V := ∀ {alpha d b r : ℝ} {rho : ℂ}, 0 < alpha →
    let data := V.readout () ()
    (∀ z : ℂ, (data z).1 → z.re ≤ 1 - alpha) →
    1 < d → d < b → (data rho).1 → 1 / 2 < rho.re →
    max r (max (d / 2 - b * alpha) 0) < d * (rho.re - 1 / 2) →
    ∀ᶠ Y : ℝ in atTop, Y ^ r ≤ (data 0).2 Y (Y ^ b)

private theorem rejects : ¬ arena.Law rejected := by
  intro h
  have hsmall : ∀ᶠ Y : ℝ in atTop, Y ^ (0 : ℝ) ≤ 0 :=
    h (alpha := 1 / 4) (d := 2) (b := 4) (r := 0) (rho := testZero)
      (by norm_num) test_strip (by norm_num) (by norm_num) rfl
      (by rw [testZero_re]; norm_num) (by rw [testZero_re]; norm_num)
  obtain ⟨Y, hY⟩ := hsmall.exists
  norm_num at hY

def family : Registration arena (type_of% @off_line_zero_forces_weighted_negative_mass_of_actual_strip) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@off_line_zero_forces_weighted_negative_mass_of_actual_strip, rejected, rejects⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejects
  dependence := dependence (fun _ => weightedNegativeMass psiErrorKernel)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@off_line_zero_forces_weighted_negative_mass_of_actual_strip) (Realization (signature (ℝ → ℝ → ℝ))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower.off_line_zero_forces_weighted_negative_mass_of_actual_strip.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower.FixedPower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedPower

namespace Abscissa

private def actual : Realization (signature (ℝ × (ℝ → ℝ → ℝ))) :=
  realize _ (fun _ _ z => (IsNontrivialZero z, zeroAbscissa, weightedNegativeMass psiErrorKernel))
    (fun e => nomatch e)

private def rejected : Realization (signature (ℝ × (ℝ → ℝ → ℝ))) :=
  realize _ (fun _ _ z => (z = testZero, 3 / 4, fun _ _ => 0)) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature (ℝ × (ℝ → ℝ → ℝ))
  Law V := ∀ {alpha b : ℝ}, 0 < alpha →
    let data := V.readout () ()
    (∀ z : ℂ, (data z).1 → z.re ≤ 1 - alpha) → 1 < b →
    (∀ r : ℝ, 0 < r → r < b * ((data 0).2.1 - 1 / 2) →
      ∀ᶠ Y : ℝ in atTop, Y ^ r ≤ (data 0).2.2 Y (Y ^ b)) ∧
    (∀ p C : ℝ, 0 ≤ p →
      (∃ᶠ Y : ℝ in atTop, (data 0).2.2 Y (Y ^ b) ≤ C * Y ^ p) →
      (data 0).2.1 ≤ 1 / 2 + p / b)

private theorem rejects : ¬ arena.Law rejected := by
  intro h
  have hsmall : ∃ᶠ Y : ℝ in atTop, (0 : ℝ) ≤ 1 * Y ^ (0 : ℝ) :=
    (Eventually.of_forall fun Y => by simp).frequently
  have hbound : (3 / 4 : ℝ) ≤ 1 / 2 + 0 / 2 :=
    (h (alpha := 1 / 4) (b := 2) (by norm_num) test_strip (by norm_num)).2
      0 1 (by norm_num) hsmall
  norm_num at hbound

def family : Registration arena (type_of% @weighted_negative_mass_power_criterion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_negative_mass_power_criterion, rejected, rejects⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejects
  dependence := dependence (fun _ => (zeroAbscissa, weightedNegativeMass psiErrorKernel))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_negative_mass_power_criterion) (Realization (signature (ℝ × (ℝ → ℝ → ℝ)))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower.weighted_negative_mass_power_criterion.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower.Abscissa.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Abscissa

end Reg.D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower
