import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.StaticExchange.OscillatorInverseMass
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.Positivity

/-! Source-linked coefficient variations for the oscillator spectral integral. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.StaticExchange.OscillatorInverseMass
open LeanInformationAudit Real Set MeasureTheory
open scoped ENNReal
namespace Reg.D5.S3.Quantum.StaticExchange.OscillatorInverseMass
noncomputable section

namespace Single

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ f => f + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a m : ℝ} (hm : 0 < m),
    Integrable (oscillator a m) ∧
      ∫ w in Ioi (0 : ℝ), oscillator a m w = (π / 2) * (R.readout () () a / m)

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have eq := (law (a := 0) (m := 1) (by norm_num)).2
  change (∫ w in Ioi (0 : ℝ), oscillator 0 1 w) = (π / 2) * ((0 + 1) / 1) at eq
  simp [oscillator] at eq
  linarith [Real.pi_pos]

def family : Registration arena (type_of% @oscillator_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨oscillator_integral, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), (zero_ne_one : (0 : ℝ) ≠ 1)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.StaticExchange.OscillatorInverseMass.oscillator_integral)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.StaticExchange.OscillatorInverseMass.Single.unit
  realizationName := `Reg.D5.S3.Quantum.StaticExchange.OscillatorInverseMass.Single.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.StaticExchange.OscillatorInverseMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Single

namespace Tower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ) (fun _ => ℕ → ℝ)

def actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ f n => f n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a m : ℕ → ℝ} (ha : ∀ n, 0 ≤ R.readout () () a n) (hm : ∀ n, 0 < m n),
    (∫⁻ w in Ioi (0 : ℝ), tower a m w) = ∑' n, ENNReal.ofReal ((π / 2) * (a n / m n)) ∧
    ((∫⁻ w in Ioi (0 : ℝ), tower a m w) ≠ ⊤ ↔ Summable (fun n => a n / m n))

private theorem shifted_fails : ¬arena.Law shifted := by
  intro law
  have h := (law (a := fun _ => -1) (m := fun _ => 1)
    (by intro n; change (0 : ℝ) ≤ -1 + 1; norm_num) (by simp)).2
  have zero (w : ℝ) : tower (fun _ => -1) (fun _ => 1) w = 0 := by
    have hn : oscillator (-1) 1 w ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    simp [tower, ENNReal.ofReal_of_nonpos hn]
  have finite : (∫⁻ w in Ioi (0 : ℝ), tower (fun _ => -1) (fun _ => 1) w) ≠ ⊤ := by simp [zero]
  simpa [summable_const_iff] using h.mp finite

def family : Registration arena (type_of% @tower_integral_criterion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tower_integral_criterion, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨(), (fun _ : ℕ => (0 : ℝ)), (fun _ : ℕ => (1 : ℝ)), fun h =>
      zero_ne_one (congrFun h 0)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.StaticExchange.OscillatorInverseMass.tower_integral_criterion)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.StaticExchange.OscillatorInverseMass.Tower.unit
  realizationName := `Reg.D5.S3.Quantum.StaticExchange.OscillatorInverseMass.Tower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.StaticExchange.OscillatorInverseMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Tower

end
end Reg.D5.S3.Quantum.StaticExchange.OscillatorInverseMass
