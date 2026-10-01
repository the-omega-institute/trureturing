import D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open _root_.D5.S3.Arith.ZeckendorfFutureKernel (legal value)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := List Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ H := ZMod H × ZMod H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H w => windowCoefficients H w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (_hH : 2 ≤ H),
    5 ≤ firstIndex H ∧
    2 * H < Nat.fib (firstIndex H) ∧ Nat.fib (firstIndex H) < 4 * H ∧
    (∀ A B : ZMod H, ∃ w : List Window,
      w.length ≤ lengthBound H ∧ w ≠ [] ∧ firstTwoZero w ∧ Success w ∧
      R.readout () H w = (A, B) ∧
      (∀ u v : ZMod H, value u v (flatten w) = A * u + B * v) ∧
      (∀ (epsilon : Bool) (p : List Window), legal epsilon (flatten p) →
        ∃ N : Nat, 0 < N ∧ initialized epsilon (p ++ w) = some N)) ∧
    D H ≤ D00 H ∧ D00 H ≤ (lengthBound H : WithTop Nat) ∧
    lengthBound H ≤ 2 * Nat.log 2 H + 5 ∧
    (lengthBound H : Real) ≤ (7 / Real.log 2) * Real.log (H : Real)

theorem actual_law : arena.Law actual := by
  intro H hH
  simpa only [actual, realize] using result H hH

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, _, _, _, _, hc, _⟩ := (h 2 (by omega)).2.2.2.1 1 0
  have hh : (0 : ZMod 2) = 1 := congrArg Prod.fst hc
  exact (by decide : (0 : ZMod 2) ≠ 1) hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, [.high], [.zero, .middle], ?_⟩
    change windowCoefficients 2 [.high] ≠ windowCoefficients 2 [.zero, .middle]
    decide

register_information_theorem
  _root_.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.result in arena
  readout via (realize signature
    (fun _ H w => windowCoefficients H w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "arg", "arg", "arg", "fn", "arg",
      "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg",
      "fn", "arg"], stateBinder := 4}] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
