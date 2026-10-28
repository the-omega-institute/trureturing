import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualIntegerHeightJump
import Reg.D5.S3.Arith.Robin.ActualIntegerLogEnvelope
import Mathlib.Data.Nat.Prime.Infinite

/-! The full integer and eta families retain the source hypotheses and actual readouts. -/

namespace Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump

open _root_.D5.S3.Arith.Robin.ActualIntegerHeightJump
open _root_.D5.S3.Arith.Robin.OriginalFirstClockTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology

noncomputable section

abbrev objectiveSignature := ActualIntegerLogEnvelope.signature
abbrev objectiveActual := ActualIntegerLogEnvelope.actual

def observedHeight (R : Realization objectiveSignature) (eta : ℝ) (n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ eta * (R.readout () () n - Real.eulerMascheroniConstant)

abbrev jumpArena : Arena where
  signature := objectiveSignature
  Law R := ∀ {eta : ℝ}, 0 < eta → eta < 1 / 2 →
    ∃ A : ℝ, 1 < A ∧ ∀ m : ℕ, 0 < m → A ≤ Real.log (m : ℝ) →
      Real.eulerMascheroniConstant < R.readout () () m →
      (∃ q, MaximalPrimePower m q) ∧ ∀ q, MaximalPrimePower m q →
        3 ≤ m / q ∧ 0 < divisorLog m - divisorLog (m / q) ∧
        observedHeight R eta m - observedHeight R eta (m / q) ≤
          (Real.log (m : ℝ)) ^ eta * (divisorLog m - divisorLog (m / q)) ∧
        (Real.log (m : ℝ)) ^ eta * (divisorLog m - divisorLog (m / q)) ≤
          (Real.log (m : ℝ)) ^ (eta - 1) * Real.log (Real.log (m : ℝ))

def jumpRejected : Realization objectiveSignature :=
  realize objectiveSignature (fun _ _ _ => Real.eulerMascheroniConstant + 1)
    (fun e => nomatch e)

theorem jump_rejected_law : ¬ jumpArena.Law jumpRejected := by
  intro h
  obtain ⟨A, hA, h⟩ := h (eta := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max 3 ⌈Real.exp A⌉₊)
  have he : Real.exp A ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 3 _).trans hpN)
  have hlarge : A ≤ Real.log (p : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos A) he
  have hF : Real.eulerMascheroniConstant < jumpRejected.readout () () p := by
    change Real.eulerMascheroniConstant < Real.eulerMascheroniConstant + 1
    linarith
  have hmax : MaximalPrimePower p p := by simp [MaximalPrimePower, hp.primeFactors]
  have hh := (h p hp.pos hlarge hF).2 p hmax |>.1
  norm_num [Nat.div_self hp.pos] at hh

def jumpFamily : Registration jumpArena (type_of% @eventual_actual_height_jump) where
  actual := objectiveActual
  bridge := Iff.rfl
  variation := ⟨eventual_actual_height_jump, jumpRejected, jump_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨jumpRejected, ?_, rfl, jump_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := ActualIntegerLogEnvelope.actual_dependence

abbrev heightSignature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def heightActual : Realization heightSignature :=
  realize heightSignature (fun _ eta n => actualHeight eta n) (fun e => nomatch e)

abbrev crossingArena : Arena where
  signature := heightSignature
  Law R := ∀ {eta : ℝ}, 0 < eta → eta < 1 / 2 →
    (∀ T : ℝ, ∃ m : ℕ, 3 ≤ m ∧ T ≤ R.readout () eta m) →
    ∃ crossing : ℝ → ℕ,
      (∀ T : ℝ, 3 ≤ crossing T ∧ T ≤ R.readout () eta (crossing T) ∧
        ∀ n : ℕ, 3 ≤ n → n < crossing T → R.readout () eta n < T) ∧
      Tendsto crossing atTop atTop ∧
      Tendsto (fun T : ℝ => (Real.log (crossing T : ℝ)) ^ (eta - 1) *
        Real.log (Real.log (crossing T : ℝ))) atTop (𝓝 0) ∧
      (∀ᶠ T : ℝ in atTop, T ≤ R.readout () eta (crossing T) ∧
        R.readout () eta (crossing T) < T +
          (Real.log (crossing T : ℝ)) ^ (eta - 1) * Real.log (Real.log (crossing T : ℝ))) ∧
      Tendsto (fun T : ℝ => R.readout () eta (crossing T) - T) atTop (𝓝 0)

def crossingRejected : Realization heightSignature :=
  realize heightSignature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

theorem crossing_rejected_law : ¬ crossingArena.Law crossingRejected := by
  intro h
  have hunbounded : ∀ T : ℝ, ∃ m : ℕ, 3 ≤ m ∧ T ≤ crossingRejected.readout () (1 / 4) m := by
    intro T
    obtain ⟨m, hm⟩ := exists_nat_ge (max T 3)
    refine ⟨m, ?_, (le_max_left T 3).trans hm⟩
    exact_mod_cast (le_max_right T 3).trans hm
  obtain ⟨crossing, hspec, _, _, _, hlimit⟩ :=
    h (eta := 1 / 4) (by norm_num) (by norm_num) hunbounded
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (hlimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨k, hk⟩ := exists_nat_ge B
  let T : ℝ := k + 1 / 2
  have hBT : B ≤ T := by dsimp [T]; linarith
  have hlow := (hspec T).2.1
  change T ≤ (crossing T : ℝ) at hlow
  have hklt : k < crossing T := by
    exact_mod_cast (show (k : ℝ) < (crossing T : ℝ) by dsimp [T] at hlow; linarith)
  have hgap : (k : ℝ) + 1 ≤ (crossing T : ℝ) := by exact_mod_cast hklt
  have hsmall := hB T hBT
  change (crossing T : ℝ) - T < 1 / 4 at hsmall
  dsimp [T] at hsmall
  linarith

theorem height_dependence : ObservationalDependence heightSignature heightActual := by
  intro i
  refine ⟨0, 0, 3, ?_⟩
  change actualHeight 0 0 ≠ actualHeight 0 3
  simp only [actualHeight, Real.rpow_zero, one_mul]
  have hz : originalObjective 0 = 0 := by simp [originalObjective]
  rw [hz]
  linarith [ActualIntegerLogEnvelope.objective_three_pos]

def crossingFamily : Registration crossingArena (type_of% @first_crossing_calibration) where
  actual := heightActual
  bridge := Iff.rfl
  variation := ⟨first_crossing_calibration, crossingRejected, crossing_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨crossingRejected, ?_, rfl, crossing_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := height_dependence

def jumpAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_actual_height_jump) (Realization objectiveSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualIntegerHeightJump.eventual_actual_height_jump.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump.jumpFamily
  realizationSource := none
  generated := false
  arena := .source ⟨jumpArena⟩
  objectArena := .source ⟨jumpArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source jumpArena ⟨jumpFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize objectiveSignature objectiveActual.readout objectiveActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualIntegerHeightJump
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "body", "domain", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def crossingAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_crossing_calibration) (Realization heightSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualIntegerHeightJump.first_crossing_calibration.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump.crossingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨crossingArena⟩
  objectArena := .source ⟨crossingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source crossingArena ⟨crossingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize heightSignature heightActual.readout heightActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualIntegerHeightJump
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "arg", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev divisorSignature := ActualIntegerLogEnvelope.signature

def divisorActual : Realization divisorSignature :=
  realize divisorSignature (fun _ _ n => divisorLog n) (fun e => nomatch e)

abbrev divisorArena : Arena where
  signature := divisorSignature
  Law R := ∀ {n : ℕ}, 0 < n → R.readout () () n ≤ Real.log (n : ℝ)

def divisorRejected : Realization divisorSignature :=
  realize divisorSignature (fun _ _ n => Real.log (n : ℝ) + 1) (fun e => nomatch e)

theorem divisor_rejected_law : ¬ divisorArena.Law divisorRejected := by
  intro h
  have := h (n := 1) (by norm_num)
  change Real.log (1 : ℝ) + 1 ≤ Real.log (1 : ℝ) at this
  linarith

def divisorFamily : Registration divisorArena (type_of% @divisor_log_le_log) where
  actual := divisorActual
  bridge := Iff.rfl
  variation := ⟨divisor_log_le_log, divisorRejected, divisor_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨divisorRejected, ?_, rfl, divisor_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 3, ?_⟩
    change divisorLog 1 ≠ divisorLog 3
    have hs : (ArithmeticFunction.sigma 1 3 : ℝ) = 4 := by norm_num [ArithmeticFunction.sigma]
    simp only [divisorLog, ArithmeticFunction.sigma_one, Nat.cast_one, div_one, Real.log_one, hs]
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)).ne

def divisorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@divisor_log_le_log) (Realization divisorSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualIntegerHeightJump.divisor_log_le_log.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump.divisorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨divisorArena⟩
  objectArena := .source ⟨divisorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source divisorArena ⟨divisorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize divisorSignature divisorActual.readout divisorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualIntegerHeightJump
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms divisorAudit

#print axioms jumpFamily
#print axioms crossingFamily
#print axioms jumpAudit
#print axioms crossingAudit

end
end Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump
