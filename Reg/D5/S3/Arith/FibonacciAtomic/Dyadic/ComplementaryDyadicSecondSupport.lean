import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport

open _root_.D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State a := Fin (2 ^ a + 1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
    (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
    let t := Finset.univ.inf' (by exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p
    t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2 →
      ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
        2 * ((2 : ℝ) ^ a - 1) ≤ R.readout () a p

def actual : Realization signature :=
  realize signature (fun _ _ p => cost p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let p : Fin (2 ^ 3 + 1) → ℝ := fun i => if i = 0 then 1 else 0
  have hp : ∀ i, 0 ≤ p i := by intro i; simp only [p]; split_ifs <;> norm_num
  have hs : ∑ i, p i = 1 := by simp [p]
  let t := Finset.univ.inf' (by exact ⟨0, Finset.mem_univ _⟩) p
  have ht : t = 0 := by
    apply le_antisymm
    · have H := Finset.inf'_le p (Finset.mem_univ (1 : Fin (2 ^ 3 + 1)))
      simpa [p, t] using H
    · exact Finset.le_inf' _ p (fun i _ => hp i)
  have H := h 3 (by decide) p hp hs
  change t ≤ ((2 : ℝ) ^ 3 - 1) / ((2 : ℝ) ^ 3) ^ 2 →
    ((2 : ℝ) ^ 3 * ((3 : ℝ) + 2) + 2 * ((2 : ℝ) ^ 3) ^ 2) * t -
      2 * ((2 : ℝ) ^ 3 - 1) ≤ -100 at H
  norm_num [ht] at H

def proof_record : Registration arena
    (∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      let t := Finset.univ.inf' (by exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p
      t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2 →
        ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
          2 * ((2 : ℝ) ^ a - 1) ≤ cost p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.result,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨0, (fun _ => 0), (fun _ => 1 / 2), ?_⟩
    have hz : cost (fun _ : Fin (2 ^ 0 + 1) => (0 : ℝ)) = 0 := by
      simp [cost, _root_.D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual]
    have H := _root_.D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope.cost_ge_one
      2 (by decide) (fun _ => 1 / 2) (by norm_num) (by norm_num)
    change cost (fun _ : Fin (2 ^ 0 + 1) => (0 : ℝ)) ≠ cost (fun _ => 1 / 2)
    rw [hz]
    exact ne_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) H)

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.result
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => cost p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
