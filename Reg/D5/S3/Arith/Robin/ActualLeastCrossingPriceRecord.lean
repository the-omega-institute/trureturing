import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
import Reg.D5.S3.Arith.Robin.ActualIntegerHeightJump

namespace Reg.D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord

open _root_.D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature := ActualIntegerHeightJump.heightSignature
abbrev actual := ActualIntegerHeightJump.heightActual

open _root_.D5.S3.Arith.Robin.ActualIntegerHeightJump
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin

abbrev priceArena : Arena where
  signature := signature
  Law R :=
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 2 →
      ∀ T : ℝ, T0 ≤ T → ∀ m : ℕ, 3 ≤ m → T ≤ R.readout () eta m →
        (∀ n : ℕ, 3 ≤ n → n < m → R.readout () eta n < T) →
        let X := Real.log (m : ℝ)
        let L := Real.log X
        let lam := (1 - (39 / 20 : ℝ) * eta) / (X * L)
        let lam0 := 1 / (40 * X * L)
        0 < lam ∧ 0 < lam0 ∧
        (∀ n : ℕ, 0 < n → n < m →
          goldenResourceObjective lam n < goldenResourceObjective lam m) ∧
        (∀ n : ℕ, 0 < n → n < m →
          goldenResourceObjective lam0 n < goldenResourceObjective lam0 m) ∧
        (∀ p j : ℕ, p.Prime → 1 ≤ j → j ≤ m.factorization p →
          (p : ℝ) ^ j * Real.log p < 40 * X * L) ∧
        m ∣ ActualTwoPriceDefect.strictInteger lam0 ∧ 5040 ∣ m

def priceRejected : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

theorem price_rejected_law : ¬ priceArena.Law priceRejected := by
  rintro ⟨T0, hT0, h⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max ⌈T0⌉₊ 5041)
  have hpN' : 5041 ≤ p := (le_max_right _ _).trans hpN
  have hTp : T0 ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hpN)
  have hleast : ∀ n : ℕ, 3 ≤ n → n < p → priceRejected.readout () (1 / 4) n < p := by
    intro n hn hnm
    change (n : ℝ) < (p : ℝ)
    exact_mod_cast hnm
  have hh := h (1 / 4) (by norm_num) (by norm_num) p hTp p (by omega)
    (by change (p : ℝ) ≤ (p : ℝ); rfl) hleast
  have hd : 5040 ∣ p := hh.2.2.2.2.2.2
  rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega

def priceFamily : Registration priceArena (type_of% @uniform_actual_least_crossing_price_record) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_actual_least_crossing_price_record, priceRejected, price_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨priceRejected, ?_, rfl, price_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := ActualIntegerHeightJump.height_dependence

def priceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_actual_least_crossing_price_record) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_price_record.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord.priceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨priceArena⟩
  objectArena := .source ⟨priceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source priceArena ⟨priceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
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

abbrev tailArena : Arena where
  signature := signature
  Law R := ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T0 A : ℝ, 0 < T0 ∧ 0 < A ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 2 →
        ∀ T : ℝ, T0 ≤ T → ∀ m : ℕ, 3 ≤ m →
          T ≤ R.readout () eta m →
          (∀ n : ℕ, 3 ≤ n → n < m → R.readout () eta n < T) →
          A ≤ Real.log (m : ℝ) →
          5040 ∣ m ∧
            Real.sqrt (_root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime m : ℝ) *
                Real.log (_root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime m) *
                _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.tail m ≤
              2 * Real.sqrt (79 / 80 : ℝ) + epsilon

theorem tail_rejected_law : ¬ tailArena.Law priceRejected := by
  intro h
  obtain ⟨T0, A, hT0, hA, h⟩ := h 1 (by norm_num)
  obtain ⟨p, hpN, hp⟩ :=
    Nat.exists_infinite_primes (max (max ⌈T0⌉₊ 3) ⌈Real.exp A⌉₊)
  have hupper : max ⌈T0⌉₊ 3 ≤ max (max ⌈T0⌉₊ 3) ⌈Real.exp A⌉₊ :=
    le_max_left _ _
  have hceilT : ⌈T0⌉₊ ≤ p :=
    (le_max_left _ _).trans (hupper.trans hpN)
  have hceilExp : ⌈Real.exp A⌉₊ ≤ p :=
    (le_max_right _ _).trans hpN
  have hp3 : 3 ≤ p :=
    (le_max_right ⌈T0⌉₊ 3).trans
      (hupper.trans hpN)
  have hTp : T0 ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilT)
  have hexpA : Real.exp A ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilExp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hAp : A ≤ Real.log (p : ℝ) :=
    (Real.le_log_iff_exp_le hp0).mpr hexpA
  have hleast : ∀ n : ℕ, 3 ≤ n → n < p →
      priceRejected.readout () (1 / 2) n < p := by
    intro n hn hnm
    change (n : ℝ) < (p : ℝ)
    exact_mod_cast hnm
  have hself : (p : ℝ) ≤ priceRejected.readout () (1 / 2) p := by
    rfl
  have hh := h (1 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2) p hTp p hp3
    hself hleast hAp
  have hd : 5040 ∣ p := hh.1
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · norm_num at h
  · subst p
    norm_num at hp

def tailFamily : Registration tailArena (type_of% @uniform_actual_least_crossing_5040_tail_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_actual_least_crossing_5040_tail_budget, priceRejected, tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨priceRejected, ?_, rfl, tail_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := ActualIntegerHeightJump.height_dependence

def tailAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_actual_least_crossing_5040_tail_budget) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_5040_tail_budget.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms priceAudit
#print axioms tailAudit

end
end Reg.D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
