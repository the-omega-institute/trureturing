import D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the triangular integral transform. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp

namespace Average

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x f => removeAverage f x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, removeAverage]

namespace Ramp

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n x : ℝ} (hn : 1 ≤ n) (hx : 0 < x),
    R.readout () x (ramp n) = max (1 - n / x) 0

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have he := h (n := 1) (x := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @removeAverage_ramp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@removeAverage_ramp, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@removeAverage_ramp) (Realization signature) Unit Unit where
  unitName := (`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.removeAverage_ramp).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.Average.Ramp.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Ramp

namespace Sqrt

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℝ} {C x : ℝ} (hx : 1 ≤ x)
    (hbound : ∀ t ∈ Icc 1 x, |f t| ≤ C * Real.sqrt t),
    |R.readout () x f| ≤ 7 * C / 3 * Real.sqrt x - 4 * C / (3 * x)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have he := h (f := fun _ => 0) (C := 0) (x := 1) (by norm_num)
    (by intro t ht; simp)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @removeAverage_sqrt_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@removeAverage_sqrt_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@removeAverage_sqrt_bound) (Realization signature) Unit Unit where
  unitName := (`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.removeAverage_sqrt_bound).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.Average.Sqrt.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sqrt

namespace Main

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ) {x : ℝ} (hx : 0 < x),
    R.readout () x (fun t => t * Real.log t - a * t) = x / 2 - (a + 1 / 2) / x

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have he := h 0 (x := 1) (by norm_num)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @removeAverage_main) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@removeAverage_main, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@removeAverage_main) (Realization signature) Unit Unit where
  unitName := (`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.removeAverage_main).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.Average.Main.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Main

end Average

namespace Endpoints

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => Real.sqrt t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B a b x : ℝ} (hB : 0 ≤ B) (ha : 0 < a) (hx : x ∈ Icc a b),
    min (A - B / a - a / 2 + Real.sqrt a)
      (A - B / b - b / 2 + Real.sqrt b) ≤ A - B / x - x / 2 + R.readout () () x

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have he := h (A := 0) (B := 0) (a := 1) (b := 1) (x := 1)
    (by norm_num) (by norm_num) (by constructor <;> norm_num)
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @affine_sqrt_ge_endpoints) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_sqrt_ge_endpoints, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@affine_sqrt_ge_endpoints) (Realization signature) Unit Unit where
  unitName := (`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.affine_sqrt_ge_endpoints).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp.Endpoints.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoints

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
