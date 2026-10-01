import D5.S3.Arith.FibonacciAtomic.MertensBoundary
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.MertensBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Asymptotics
open scoped BigOperators

namespace Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => boundary x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x ^ (2 : ℕ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ a : ℝ, 0 < a →
    ((r.readout () () =O[atTop] (fun X : ℝ => X ^ a)) ↔
      coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ∧
    ((coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ↔
      coprimeMertens 1 =O[atTop] (fun X : ℝ => X ^ a))

theorem restricted_linear : coprimeMertens 70 =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  classical
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Real.rpow_one, Real.norm_eq_abs, one_mul, abs_of_nonneg hx]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        |if n.Coprime 70 then (ArithmeticFunction.moebius n : ℝ) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      split_ifs
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      · norm_num
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := ((h 1 (by norm_num)).1).mpr restricted_linear
  change (fun x : ℝ => x ^ (2 : ℕ)) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) at hb
  obtain ⟨C, hC⟩ := isBigO_iff.mp hb
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  let x := max (max T (|C| + 1)) 1
  have hx1 : 1 ≤ x := le_max_right _ _
  have hxT : T ≤ x := (le_max_left _ _).trans (le_max_left _ _)
  have hxC : |C| + 1 ≤ x := (le_max_right _ _).trans (le_max_left _ _)
  have hx : 0 ≤ x := by linarith
  have he := hT x hxT
  simp only [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg (sq_nonneg x),
    abs_of_nonneg hx] at he
  have hc := le_abs_self C
  nlinarith

def registration : Registration arena
    (∀ a : ℝ, 0 < a →
      ((boundary =O[atTop] (fun X : ℝ => X ^ a)) ↔
        coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ∧
      ((coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ↔
        coprimeMertens 1 =O[atTop] (fun X : ℝ => X ^ a))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨power_bounds_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (7 : ℝ), ?_⟩
    change boundary 0 ≠ boundary 7
    norm_num [boundary, Finset.sum_Ioc_succ_top]

register_information_theorem power_bounds_iff in arena
  readout via (realize signature (fun _ _ x => boundary x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.MertensBoundary
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary
