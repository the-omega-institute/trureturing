import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.JMJPairLosing
import Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix Classical
namespace Reg.D5.S3.Observer.CubicGain.JMJPairLosing
open _root_.D5.S3.Observer.CubicGain.MixedTripleExclusion
open _root_.D5.S3.Observer.CubicGain.JMJPairLosing
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion

namespace JMJPair
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Bool)
  (fun _ => Finset World3) (fun _ => Bool)
def actual : Realization signature := realize signature
  (fun _ p T => decide (Losing p.1 T [true, false, true, p.2])) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 3 ≤ n) (E : Bool) (z v : ℝ)
    (W Z : World3) (_hne : W ≠ Z)
    (_hW : readings W [true, false, true, E] = ![0, 24, 48, z, v])
    (_hZ : readings Z [true, false, true, E] = ![0, 24, 48, z, v]),
    R.readout () ⟨n, E⟩ {W, Z} = true ↔
      W.drift = Z.drift ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ n →
        (gain 3 W.coeff).eval ((4 + j : ℕ) : ℝ) = 0 ∧
        (gain 3 Z.coeff).eval ((4 + j : ℕ) : ℝ) = 0) ∧
      (∀ F : Bool, readAt W [true, false, true, E, F] 5 =
        readAt Z [true, false, true, E, F] 5)
private def leftWorld : World3 := legalWorld 2 (4/3) (by norm_num) (by norm_num)
  ![0, 924/25, -286/25, 22/25] (by intro h; have := congrFun h 3; norm_num at this) 0
private def rightWorld : World3 := legalWorld (1/3) 3 (by norm_num) (by norm_num)
  ![0, 504/25, -156/25, 12/25] (by intro h; have := congrFun h 3; norm_num at this) 0
private theorem pair_ne : leftWorld ≠ rightWorld := by
  intro h
  have := congrArg (fun W : World3 => W.coeff 3) h
  norm_num [leftWorld, rightWorld, legalWorld] at this
private theorem pair_history :
    readings leftWorld [true, false, true, true] = ![0, 24, 48, 936/25, 144/5] ∧
    readings rightWorld [true, false, true, true] = ![0, 24, 48, 936/25, 144/5] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [leftWorld, rightWorld, legalWorld, readings, readAt, gain,
      Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, Fin.sum_univ_succ, acquisition, Raw,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      sourceChart, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]
private theorem pair_conditions :
    leftWorld.drift = rightWorld.drift ∧
    (∀ j : ℕ, 2 ≤ j → j ≤ 3 →
      (gain 3 leftWorld.coeff).eval ((4 + j : ℕ) : ℝ) = 0 ∧
      (gain 3 rightWorld.coeff).eval ((4 + j : ℕ) : ℝ) = 0) ∧
    (∀ F : Bool, readAt leftWorld [true, false, true, true, F] 5 =
      readAt rightWorld [true, false, true, true, F] 5) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj hjn
    interval_cases j <;>
      norm_num [leftWorld, rightWorld, legalWorld, gain, Polynomial.ofFn_eq_sum_monomial,
        Polynomial.eval_finsetSum, Polynomial.eval_monomial, Fin.sum_univ_succ]
  · intro F
    cases F <;>
      norm_num [leftWorld, rightWorld, legalWorld, readAt, gain,
        Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
        Polynomial.eval_monomial, Fin.sum_univ_succ, acquisition, Raw,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        sourceChart, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 3 (by omega) true (936/25) (144/5) leftWorld rightWorld pair_ne
    pair_history.1 pair_history.2).mpr pair_conditions
  simp [rejected, realize] at hh

def family : Registration arena (type_of% @jmj_pair_losing_iff) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
    using jmj_pair_losing_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨3, true⟩, ∅, {leftWorld, rightWorld}, ?_⟩
    intro h
    have hp := (jmj_pair_losing_iff 3 (by omega) true (936/25) (144/5)
      leftWorld rightWorld pair_ne pair_history.1 pair_history.2).mpr pair_conditions
    have he : ¬ Losing 3 (∅ : Finset World3) [true, false, true, true] := by
      intro hh
      have hg := hh.1
      norm_num at hg
    simp [actual, realize, hp, he] at h

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@jmj_pair_losing_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.JMJPairLosing.jmj_pair_losing_iff.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.JMJPairLosing.JMJPair.family
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
    (fun _ p T => decide (Losing p.1 T [true, false, true, p.2])) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.JMJPairLosing
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end JMJPair

end Reg.D5.S3.Observer.CubicGain.JMJPairLosing
