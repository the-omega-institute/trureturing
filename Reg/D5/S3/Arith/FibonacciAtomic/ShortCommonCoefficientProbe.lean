import D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
open _root_.D5.S3.Analytic.GoldenEulerBetaZeckendorf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ H := ZMod H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H n => (shiftedFibSum n : ZMod H)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ H _ => (0 : ZMod H)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (_hH : 2 ≤ H),
    let j := firstIndex H
    let q := Nat.fib j
    5 ≤ j ∧ 2 * H < q ∧ q < 4 * H ∧
      ∀ A B : ZMod H, ∃ n : Nat,
        H ≤ n ∧ n < H * (q + 1) ∧
        (n : ZMod H) = B ∧ R.readout () H n = A

theorem actual_law : arena.Law actual := by
  intro H hH
  simpa only [actual, realize] using bounded_coefficient_pair H hH

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, _, _, _, hn⟩ := (h 2 (by omega)).2.2.2 1 0
  have hc : (0 : ZMod 2) = 1 := hn
  exact (by decide : (0 : ZMod 2) ≠ 1) hc

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change (shiftedFibSum 0 : ZMod 2) ≠ (shiftedFibSum 1 : ZMod 2)
    norm_num [shiftedFibSum, Nat.zeckendorf_succ, Nat.greatestFib]

register_information_theorem bounded_coefficient_pair in arena
  readout via (realize signature
    (fun _ H n => (shiftedFibSum n : ZMod H)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "body", "arg", "arg", "arg",
      "body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg"], stateBinder := 6}] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
