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

#print axioms crossingFamily
#print axioms crossingAudit

end
end Reg.D5.S3.Arith.Robin.ActualLeastCrossing5040
