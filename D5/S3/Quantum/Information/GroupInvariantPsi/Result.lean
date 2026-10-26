/- GID: D5/S3/Quantum/Information/GroupInvariantPsi/Result
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GroupInvariantPsi/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.GroupTheory.Perm.Fin]
   utility: none
   digest: Faithful four-level states with a two-element permutation symmetry have an asymptotic overlap that is not differentiable. -/


import D5.S3.Quantum.Information.GroupInvariantPsi.Sandwich
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin
open Finset Filter
open scoped BigOperators Topology MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.Information.GroupInvariantPsi.Result
open Defs
private def p : Fin 4 → ℝ := ![16 / 30, 9 / 30, 4 / 30, 1 / 30]
private def q : Fin 4 → ℝ := ![4 / 30, 1 / 30, 9 / 30, 16 / 30]
private def flip : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
private def action : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 4) where
  toFun g := if g = 1 then 1 else flip
  map_one' := by simp
  map_mul' := by decide
private def branch (s : ℝ) : ℝ := ∑ i, p i ^ s * q i ^ (1 - s)
private lemma p_pos (i : Fin 4) : 0 < p i := by fin_cases i <;> norm_num [p]
private lemma q_pos (i : Fin 4) : 0 < q i := by fin_cases i <;> norm_num [q]
private lemma branch_half : branch (1 / 2) = 7 / 10 := by
  simp only [branch]
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simp_rw [← Real.mul_rpow (p_pos _).le (q_pos _).le, ← Real.sqrt_eq_rpow]
  norm_num [p, q, Fin.sum_univ_succ, Real.sqrt_div]
private lemma branch_derivative :
    HasDerivAt branch ((1 / 5 : ℝ) * Real.log (4 / 3)) (1 / 2) := by
  have hd (i : Fin 4) : HasDerivAt (fun s : ℝ => p i ^ s * q i ^ (1 - s))
      ((Real.log (p i) - Real.log (q i)) *
        (p i ^ (1 / 2 : ℝ) * q i ^ (1 / 2 : ℝ))) (1 / 2) := by
    convert ((hasDerivAt_id (1 / 2 : ℝ)).const_rpow (p_pos i)).mul
      (((hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)).sub (hasDerivAt_id _)).const_rpow (q_pos i)) using 1 <;>
      first | rfl | (norm_num <;> ring)
  have hh := HasDerivAt.fun_sum (u := univ) (fun i _ => hd i)
  have hlog2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  have hlog9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    convert Real.log_pow (3 : ℝ) 2 using 1 <;> norm_num
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0) using 1 <;> norm_num
  have hlog15 : Real.log (15 : ℝ) = Real.log 3 + Real.log 5 := by
    convert Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0) using 1 <;> norm_num
  have hlog30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    calc
      _ = Real.log 2 + Real.log 15 := by
        convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (15 : ℝ) ≠ 0) using 1 <;> norm_num
      _ = _ := by rw [hlog15]; ring
  convert hh using 1
  · rfl
  · simp_rw [← Real.mul_rpow (p_pos _).le (q_pos _).le, ← Real.sqrt_eq_rpow]
    norm_num [p, q, Fin.sum_univ_succ, Real.sqrt_div, Real.log_div, hlog2, hlog16, hlog9, hlog8, hlog10, hlog15, hlog30]
    ring
private lemma branch_pos (s : ℝ) : 0 < branch s := by
  exact sum_pos (fun i _ => mul_pos (Real.rpow_pos_of_pos (p_pos i) _)
    (Real.rpow_pos_of_pos (q_pos i) _)) univ_nonempty

private lemma log_branch_derivative :
    HasDerivAt (fun s => Real.log (branch s))
      ((2 / 7 : ℝ) * Real.log (4 / 3)) (1 / 2) := by
  convert branch_derivative.log (branch_pos _).ne' using 1
  rw [branch_half]
  ring

private lemma max_slopes {f g : ℝ → ℝ} {x a b : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) (heq : f x = g x) :
    Tendsto (slope (fun t => max (f t) (g t)) x) (𝓝[<] x) (𝓝 (min a b)) ∧
    Tendsto (slope (fun t => max (f t) (g t)) x) (𝓝[>] x) (𝓝 (max a b)) := by
  have hflr := hasDerivAt_iff_tendsto_slope_left_right.mp hf
  have hglr := hasDerivAt_iff_tendsto_slope_left_right.mp hg
  constructor
  · apply (hflr.1.min hglr.1).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field, heq, max_self]
    rw [min_div_div_right_of_nonpos (sub_nonpos.mpr hy.le), max_sub_sub_right]
  · apply (hflr.2.max hglr.2).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field, heq, max_self]
    rw [max_div_div_right (sub_nonneg.mpr hy.le), max_sub_sub_right]

/-- The two logarithmic overlap branches of the four-level example. -/
def counterexamplePsi (s : ℝ) : ℝ :=
  max (Real.log (branch s)) (Real.log (branch (1 - s)))

/-- The left and right difference quotients converge to distinct explicit values. -/
theorem one_sided_derivs :
    Tendsto (slope counterexamplePsi (1 / 2)) (𝓝[<] (1 / 2 : ℝ))
      (𝓝 (-((2 / 7 : ℝ) * Real.log (4 / 3)))) ∧
    Tendsto (slope counterexamplePsi (1 / 2)) (𝓝[>] (1 / 2 : ℝ))
      (𝓝 ((2 / 7 : ℝ) * Real.log (4 / 3))) := by
  have hd2 : HasDerivAt (fun s => Real.log (branch (1 - s)))
      (-((2 / 7 : ℝ) * Real.log (4 / 3))) (1 / 2) := by
    convert log_branch_derivative.comp_of_eq (1 / 2)
      ((hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)).sub (hasDerivAt_id _)) (by norm_num) using 1 <;>
      first | rfl | (norm_num <;> ring)
  have hc : 0 < (2 / 7 : ℝ) * Real.log (4 / 3) :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have h := max_slopes log_branch_derivative hd2 (by norm_num)
  have horder : -((2 / 7 : ℝ) * Real.log (4 / 3)) ≤ (2 / 7 : ℝ) * Real.log (4 / 3) := by linarith
  have hfun : (fun t => max (Real.log (branch t)) (Real.log (branch (1 - t)))) = counterexamplePsi := rfl
  rw [hfun, min_eq_right horder, max_eq_left horder] at h
  exact h

private lemma maxCoeff_eq (s : ℝ) :
    Sandwich.maxCoeff action p q s = max (branch s) (branch (1 - s)) := by
  classical
  have hall : (univ : Finset (Multiplicative (ZMod 2))) =
      {1, Multiplicative.ofAdd (1 : ZMod 2)} := by decide
  have he : Sandwich.componentCoeff action p q s 1 = branch s := by
    simp [Sandwich.componentCoeff, branch]
  have ht : Sandwich.componentCoeff action p q s (Multiplicative.ofAdd (1 : ZMod 2)) =
      branch (1 - s) := by
    norm_num [Sandwich.componentCoeff, action, flip, branch, p, q,
      Fin.sum_univ_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    ring
  unfold Sandwich.maxCoeff
  simp [hall, Finset.sup'_insert, he, ht]

private lemma log_maxCoeff (s : ℝ) :
    Real.log (Sandwich.maxCoeff action p q s) = counterexamplePsi s := by
  rw [maxCoeff_eq]
  unfold counterexamplePsi
  rcases le_total (branch s) (branch (1 - s)) with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log (branch_pos _) h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log (branch_pos _) h)]

/-- Faithful four-level states with a two-element permutation symmetry refute
universal differentiability of the asymptotic group-invariant overlap. -/
theorem result : ¬ claim := by
  intro hclaim
  let u := Mixture.permutationRepresentation action
  let ρ₀ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun i => (p i : ℂ)
  let ρ₁ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun i => (q i : ℂ)
  have hpdef : ρ₀.PosDef := Matrix.PosDef.diagonal fun i => by exact_mod_cast p_pos i
  have hqdef : ρ₁.PosDef := Matrix.PosDef.diagonal fun i => by exact_mod_cast q_pos i
  have hpone : Matrix.trace ρ₀ = 1 := by
    norm_num [ρ₀, Matrix.trace_diagonal, p, Fin.sum_univ_succ]
  have hqone : Matrix.trace ρ₁ = 1 := by
    norm_num [ρ₁, Matrix.trace_diagonal, q, Fin.sum_univ_succ]
  have hpsi (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
      psi u ρ₀ ρ₁ s = counterexamplePsi s :=
    (Sandwich.psi_eq_max action p q p_pos q_pos hs.1 hs.2).2.trans (log_maxCoeff s)
  have hconv (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
      Tendsto (fun n : ℕ => psiN u ρ₀ ρ₁ n s / n) atTop (𝓝 (psi u ρ₀ ρ₁ s)) := by
    change Tendsto (fun n : ℕ => psiN u ρ₀ ρ₁ n s / n) atTop
      (𝓝 (psi u ρ₀ ρ₁ s))
    rw [(Sandwich.psi_eq_max action p q p_pos q_pos hs.1 hs.2).2]
    exact (Sandwich.psi_eq_max action p q p_pos q_pos hs.1 hs.2).1
  have hd := hclaim 4 (Multiplicative (ZMod 2)) u ρ₀ ρ₁ hpdef hpone hqdef hqone hconv
  have hm : DifferentiableOn ℝ counterexamplePsi (Set.Ioo (0 : ℝ) 1) :=
    hd.congr fun s hs => (hpsi s hs).symm
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hdhalf := hm.differentiableAt (isOpen_Ioo.mem_nhds hhalf)
  have hquot := hasDerivAt_iff_tendsto_slope_left_right.mp hdhalf.hasDerivAt
  have hleft := tendsto_nhds_unique hquot.1 one_sided_derivs.1
  have hright := tendsto_nhds_unique hquot.2 one_sided_derivs.2
  have hc : 0 < (2 / 7 : ℝ) * Real.log (4 / 3) :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  linarith

end D5.S3.Quantum.Information.GroupInvariantPsi.Result
