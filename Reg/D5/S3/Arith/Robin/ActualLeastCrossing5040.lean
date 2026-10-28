import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualLeastCrossing5040
import Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump

namespace Reg.D5.S3.Arith.Robin.ActualLeastCrossing5040

open _root_.D5.S3.Arith.Robin.ActualLeastCrossing5040
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature := ActualIntegerHeightJump.heightSignature
abbrev actual := ActualIntegerHeightJump.heightActual

abbrev crossingArena : Arena where
  signature := signature
  Law R := ∃ T0 : ℝ, 0 < T0 ∧ ∀ eta : ℝ, 0 < eta → eta < 1 / 2 →
    ∀ T : ℝ, T0 ≤ T → ∀ m : ℕ, 3 ≤ m → T ≤ R.readout () eta m →
      (∀ n : ℕ, 3 ≤ n → n < m → R.readout () eta n < T) →
      30 < (ArithmeticFunction.sigma 1 m : ℝ) / m ∧
      (∀ n : ℕ, 0 < n → n < m →
        (ArithmeticFunction.sigma 1 n : ℝ) / n < (ArithmeticFunction.sigma 1 m : ℝ) / m) ∧
      5040 ∣ m

def crossingRejected : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

theorem crossing_rejected_law : ¬ crossingArena.Law crossingRejected := by
  rintro ⟨T0, hT0, h⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max ⌈T0⌉₊ 5041)
  have hpN' : 5041 ≤ p := (le_max_right _ _).trans hpN
  have hTp : T0 ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hpN)
  have hleast : ∀ n : ℕ, 3 ≤ n → n < p → crossingRejected.readout () (1 / 4) n < p := by
    intro n hn hnm
    change (n : ℝ) < (p : ℝ)
    exact_mod_cast hnm
  have hh := h (1 / 4) (by norm_num) (by norm_num) p hTp p (by omega)
    (by change (p : ℝ) ≤ (p : ℝ); rfl) hleast
  have hd : 5040 ∣ p := hh.2.2
  rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega

def crossingFamily : Registration crossingArena (type_of% @uniform_actual_least_crossing_record_5040) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_actual_least_crossing_record_5040, crossingRejected, crossing_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨crossingRejected, ?_, rfl, crossing_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := ActualIntegerHeightJump.height_dependence

def crossingAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_actual_least_crossing_record_5040) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualLeastCrossing5040.uniform_actual_least_crossing_record_5040.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualLeastCrossing5040.crossingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨crossingArena⟩
  objectArena := .source ⟨crossingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source crossingArena ⟨crossingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualLeastCrossing5040
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev escapeArena : Arena where
  signature := signature
  Law R := ∀ bound : ℝ,
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 2 →
      ∀ T : ℝ, T0 ≤ T → ∀ m : ℕ, 3 ≤ m → T ≤ R.readout () eta m →
        bound < _root_.D5.S3.Arith.Robin.ActualIntegerHeightJump.divisorLog m ∧
          Real.exp 2 ≤ Real.log (m : ℝ)

theorem escape_rejected_law : ¬ escapeArena.Law crossingRejected := by
  intro h
  obtain ⟨T0, hT0, h⟩ := h (Real.log 2)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max ⌈T0⌉₊ 3)
  have hp3 : 3 ≤ p := (le_max_right _ _).trans hpN
  have hTp : T0 ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hpN)
  have hh := (h (1 / 2) (by norm_num) le_rfl p hTp p hp3
    (by change (p : ℝ) ≤ (p : ℝ); rfl)).1
  have hs : ArithmeticFunction.sigma 1 p = p + 1 := by
    simpa [Finset.sum_range_succ, add_comm] using
      (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)
  have hbound : _root_.D5.S3.Arith.Robin.ActualIntegerHeightJump.divisorLog p ≤ Real.log 2 := by
    unfold _root_.D5.S3.Arith.Robin.ActualIntegerHeightJump.divisorLog
    rw [hs, Nat.cast_add, Nat.cast_one]
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (by exact_mod_cast hp.pos : (0 : ℝ) < p)).mpr
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  linarith

def escapeFamily : Registration escapeArena (type_of% @uniform_actual_height_escape) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_actual_height_escape, crossingRejected, escape_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨crossingRejected, ?_, rfl, escape_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := ActualIntegerHeightJump.height_dependence

def escapeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_actual_height_escape) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualLeastCrossing5040.uniform_actual_height_escape.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualLeastCrossing5040.escapeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨escapeArena⟩
  objectArena := .source ⟨escapeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source escapeArena ⟨escapeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualLeastCrossing5040
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms escapeAudit

#print axioms crossingFamily
#print axioms crossingAudit

end
end Reg.D5.S3.Arith.Robin.ActualLeastCrossing5040
