import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciRankParentHeight
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRankParentHeight

open _root_.D5.S3.Arith.Primes.FibonacciRankParentHeight
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.FibonacciRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: a numeric readout of a natural-number coordinate. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The parent bound with the doubling of the parent varied; the rank relation stays. -/
abbrev parentArena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ}, p.Prime → 5 < p → q.Prime → q ∣ fibonacciRank p →
    R.readout () () q ≤ p + 1

/-- The height bound with the power `2 ^ k` of the path length varied. -/
abbrev heightArena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime → (∃ r k, r ≤ 5 ∧ RankDescent p r k) ∧
    ∀ r k, RankDescent p r k → R.readout () () k ≤ p - 1

def parentActual : Realization signature :=
  realize signature (fun _ _ x => 2 * x) (fun e => nomatch e)

def heightActual : Realization signature :=
  realize signature (fun _ _ x => 2 ^ x) (fun e => nomatch e)

/-- The constant readout `13` replaces the doubled parent. -/
def parentRejected : Realization signature :=
  realize signature (fun _ _ _ => 13) (fun e => nomatch e)

/-- The constant readout `2` replaces the power of two. -/
def heightRejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- The Fibonacci rank of `11` is divisible by `5`: it divides `10` because `11 ∣ F₁₀ = 55`,
and it is neither `1` nor `2` because `F₁ = F₂ = 1`. -/
private theorem five_dvd_rank_eleven : 5 ∣ fibonacciRank 11 := by
  have h11 : Nat.Prime 11 := by norm_num
  have hval : fibonacciRank 11 = (rankWitness 11 h11).val := by
    unfold fibonacciRank
    rw [dif_pos h11]
  obtain ⟨hpos, hzero, hmin⟩ := (rankWitness 11 h11).2
  rw [hval]
  set r := (rankWitness 11 h11).val
  have hr10 : r ∣ 10 := (fibonacci_entry_point hpos hzero hmin).mp (by decide)
  have hrle : r ≤ 10 := Nat.le_of_dvd (by norm_num) hr10
  have hr1 : r ≠ 1 := fun h => by rw [h] at hzero; norm_num at hzero
  have hr2 : r ≠ 2 := fun h => by rw [h] at hzero; norm_num [Nat.fib_add_two] at hzero
  interval_cases r <;> simp_all <;> omega

/-- At `p = 11` and its rank parent `5`, the constant `13` exceeds `p + 1 = 12`. -/
theorem parent_rejected_law : ¬ parentArena.Law parentRejected := by
  intro h
  have hbad := h (p := 11) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    five_dvd_rank_eleven
  change (13 : ℕ) ≤ 11 + 1 at hbad
  omega

/-- At the root `p = 2` with the empty path, the constant `2` exceeds `p - 1 = 1`. -/
theorem height_rejected_law : ¬ heightArena.Law heightRejected := by
  intro h
  have hbad := (h (p := 2) Nat.prime_two).2 2 0 (RankDescent.refl Nat.prime_two)
  change (2 : ℕ) ≤ 2 - 1 at hbad
  omega

private theorem parent_dependence : ObservationalDependence signature parentActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change 2 * 0 ≠ 2 * 1
  norm_num

private theorem height_dependence : ObservationalDependence signature heightActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change 2 ^ 0 ≠ 2 ^ 1
  norm_num

def parentRegistration : Registration parentArena
    (∀ {p q : ℕ}, p.Prime → 5 < p → q.Prime → q ∣ fibonacciRank p → 2 * q ≤ p + 1) where
  actual := parentActual
  bridge := Iff.rfl
  variation := ⟨two_mul_le_of_dvd_fibonacciRank, parentRejected, parent_rejected_law⟩
  sensitivity := ⟨fun i => ⟨parentRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), parent_rejected_law⟩, fun i => nomatch i⟩
  dependence := parent_dependence

def heightRegistration : Registration heightArena
    (∀ {p : ℕ}, p.Prime → (∃ r k, r ≤ 5 ∧ RankDescent p r k) ∧
      ∀ r k, RankDescent p r k → 2 ^ k ≤ p - 1) where
  actual := heightActual
  bridge := Iff.rfl
  variation := ⟨rankDescent_to_root_and_height, heightRejected, height_rejected_law⟩
  sensitivity := ⟨fun i => ⟨heightRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), height_rejected_law⟩, fun i => nomatch i⟩
  dependence := height_dependence

/-- The parent record binds the doubled parent `2 * q` through its raw source path. -/
def parentAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_mul_le_of_dvd_fibonacciRank)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 2 * x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.FibonacciRankParentHeight.two_mul_le_of_dvd_fibonacciRank.audit
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciRankParentHeight.parentRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨parentArena⟩
  objectArena := .source ⟨parentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source parentArena ⟨parentRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 2 * x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.FibonacciRankParentHeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The height record binds the power `2 ^ k` of the path length through its raw source path. -/
def heightAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rankDescent_to_root_and_height)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 2 ^ x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.FibonacciRankParentHeight.rankDescent_to_root_and_height.audit
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciRankParentHeight.heightRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨heightArena⟩
  objectArena := .source ⟨heightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source heightArena ⟨heightRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 2 ^ x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.FibonacciRankParentHeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Primes.FibonacciRankParentHeight
