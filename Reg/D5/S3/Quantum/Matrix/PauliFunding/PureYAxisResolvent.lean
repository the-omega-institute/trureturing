import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
open _root_.D5.S3.Quantum.Matrix.PauliFunding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _a : ℝ, Σ _t : ℝ, ℝ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p j => moment p.1 p.2.1 j p.2.2) (fun e => nomatch e)

def complexActual : Realization signature :=
  realize signature (fun _ p j => complexMoment p.1 p.2.1 j p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, 0, 1, ?_⟩
  intro he
  change moment 1 0 0 1 = moment 1 0 1 1 at he
  rw [moment_boundary (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [h]) (by norm_num) 1 le_rfl] at he
  norm_num [moment, _root_.Matrix.trace_one] at he

private theorem complexDependence : ObservationalDependence signature complexActual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, 0, 1, ?_⟩
  intro he
  change complexMoment 1 0 0 1 = complexMoment 1 0 1 1 at he
  rw [complex_moment_eq_real (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    complex_moment_eq_real (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at he
  rw [moment_boundary (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [h]) (by norm_num) 1 le_rfl] at he
  norm_num [moment, _root_.Matrix.trace_one] at he

namespace Formula

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a t s : ℝ}, 0 ≤ a → a ≤ 1 → t ^ 2 ≤ 1 - a ^ 2 → 0 < s →
    ∀ j : ℕ, R.readout () ⟨a,t,s⟩ j = evenMoment (alpha a t s) (beta a t s) j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (a := 0) (t := 0) (s := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 0
  norm_num [rejected, realize, evenMoment] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_eq_evenMoment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_eq_evenMoment, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_eq_evenMoment) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Formula.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Formula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p j => moment p.1 p.2.1 j p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Formula

namespace Comparison

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a t s : ℝ}, 0 ≤ a → a ≤ 1 → t ^ 2 ≤ 1 - a ^ 2 → 0 < s →
    ∀ j : ℕ, a ^ (2 * j) / (1 + 2 * s) ^ (2 * j) ≤ R.readout () ⟨a,t,s⟩ j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (a := 0) (t := 0) (s := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_comparison, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_comparison) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Comparison.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Comparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p j => moment p.1 p.2.1 j p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Comparison

namespace Strict

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a t s : ℝ}, 0 ≤ a → a ≤ 1 → t ^ 2 ≤ 1 - a ^ 2 →
    0 < h a t → 0 < s → ∀ j : ℕ, 1 ≤ j → a ^ (2 * j) / (1 + 2 * s) ^ (2 * j) < R.readout () ⟨a,t,s⟩ j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (a := 0) (t := 0) (s := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [h]) (by norm_num) 1 le_rfl
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_strict)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_strict, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_strict) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Strict.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Strict.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p j => moment p.1 p.2.1 j p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Strict

namespace Boundary

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a t s : ℝ}, 0 ≤ a → a ≤ 1 → t ^ 2 ≤ 1 - a ^ 2 →
    h a t = 0 → 0 < s → ∀ j : ℕ, 1 ≤ j → R.readout () ⟨a,t,s⟩ j = a ^ (2 * j) / (1 + 2 * s) ^ (2 * j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (a := 1) (t := 0) (s := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [h]) (by norm_num) 1 le_rfl
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_boundary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.moment_boundary) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Boundary.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Boundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p j => moment p.1 p.2.1 j p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Boundary

namespace Complex

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a t s : ℝ}, 0 ≤ a → a ≤ 1 → t ^ 2 ≤ 1 - a ^ 2 → 0 < s →
    ∀ j : ℕ, R.readout () ⟨a,t,s⟩ j = moment a t j s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (a := 0) (t := 0) (s := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 0
  norm_num [rejected, realize, moment, _root_.Matrix.trace_one] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.complex_moment_eq_real)) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.complex_moment_eq_real, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexActual rejected rejected_law
  dependence := complexDependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.complex_moment_eq_real) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Complex.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.Complex.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p j => complexMoment p.1 p.2.1 j p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Complex

namespace SpectralData

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _a : ℝ, ℝ) (fun _ => ℝ) (fun _ => Mat)

def actual : Realization signature :=
  realize signature (fun _ p s => controlFilter p.1 p.2 s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Mat)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a t s : ℝ}, 0 ≤ a → a ≤ 1 → t ^ 2 ≤ 1 - a ^ 2 → 0 < s →
    0 < denom a t s ∧ 0 ≤ alpha a t s ∧ 0 ≤ beta a t s ∧
      R.readout () ⟨a,t⟩ s =
        !![(4*s+h a t+4*s*a)/denom a t s, 4*s*t/denom a t s;
           4*s*t/denom a t s, (4*s+h a t-4*s*a)/denom a t s] ∧
      R.readout () ⟨a,-t⟩ s = parity * R.readout () ⟨a,t⟩ s * parity ∧
      _root_.Matrix.trace (parity * R.readout () ⟨a,t⟩ s) = 2 * alpha a t s ∧
      _root_.Matrix.det (parity * R.readout () ⟨a,t⟩ s) = -beta a t s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  obtain ⟨_, _, _, he, _⟩ := hh (a := 1) (t := 0) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hz := congrArg (fun M : Mat => M 0 0) he
  norm_num [rejected, realize, h, denom] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 1, 2, ?_⟩
  intro he
  change controlFilter 1 0 1 = controlFilter 1 0 2 at he
  obtain ⟨_, _, _, hf1, _⟩ := resolvent_spectral_data (a := 1) (t := 0) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, _, _, hf2, _⟩ := resolvent_spectral_data (a := 1) (t := 0) (s := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hf1, hf2] at he
  have hz := congrArg (fun M : Mat => M 0 0) he
  norm_num [h, denom] at hz

def family : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.resolvent_spectral_data)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.resolvent_spectral_data,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.resolvent_spectral_data)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.SpectralData.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent.SpectralData.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => controlFilter p.1 p.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralData

end
end Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent
