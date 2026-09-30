import D5.S3.Arith.Robin.FibonacciRankEulerTail
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail

open Finset
open _root_.D5.S3.Arith.Robin.FibonacciRankEulerTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The prime weight varies while both bounds and the complete rank bucket remain fixed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ), 5 < d →
    (∑ p ∈ rankBucket d, R.readout () () p) ≤ 6 * (harmonic d : ℝ) / d ∧
      6 * (harmonic d : ℝ) / d ≤ 6 * (1 + Real.log d) / d

def actual : Realization signature :=
  realize signature (fun _ _ p => Real.log ((p : ℝ) / ((p : ℝ) - 1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 7 (by decide)).1
  have hb : rankBucket 7 = {13} := by
    norm_num [rankBucket, Nat.fib_add_two]
    intro k h1 h7
    interval_cases k <;> norm_num [Nat.fib_add_two]
  change (∑ _p ∈ rankBucket 7, (100 : ℝ)) ≤ 6 * (harmonic 7 : ℝ) / 7 at hh
  rw [hb] at hh
  norm_num [harmonic, Finset.sum_range_succ] at hh

def registration : Registration arena (∀ (d : ℕ), 5 < d →
    (∑ p ∈ rankBucket d, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
        6 * (harmonic d : ℝ) / d ∧
      6 * (harmonic d : ℝ) / d ≤ 6 * (1 + Real.log d) / d) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

register_information_theorem result in arena
  readout via (realize signature
    (fun _ _ p => Real.log ((p : ℝ) / ((p : ℝ) - 1))) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Robin.FibonacciRankEulerTail
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      functionOperand := true }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName == `D5.S3.Arith.Robin.FibonacciRankEulerTail.result
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true | _ => false) do
    throwError "Fibonacci rank Euler tail registration is not declaredValidated"

#print axioms registration

end

end Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail
