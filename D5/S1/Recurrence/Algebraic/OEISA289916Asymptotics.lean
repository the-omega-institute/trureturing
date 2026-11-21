import D5.S1.Recurrence.Algebraic.OEISA289916StrictIncrease
import D5.S1.Recurrence.Asymptotic.DominantRootForcing
import D5.S1.Recurrence.OEISA400645
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

noncomputable section

namespace D5.S1.Recurrence.Algebraic.OEISA289916Asymptotics

open Polynomial Asymptotics Filter
open D5.S1.Recurrence.Asymptotic.DominantRootForcing (shift aeval_apply aeval_X_sub_C_apply)

/-- If a complex polynomial has only simple roots, every sequence annihilated by it is a linear
combination of the geometric sequences of its roots. -/
private theorem geom_decomp (p : ℂ[X]) (hp : p ≠ 0) (hnd : p.roots.Nodup) (u : ℕ → ℂ)
    (hu : aeval shift p u = 0) :
    ∃ α : ℂ → ℂ, ∀ n, u n = ∑ z ∈ p.roots.toFinset, α z * z ^ n := by
  classical
  set s := p.roots.toFinset with hs
  have hsplit : Multiset.card p.roots = p.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hroots : p.roots = s.val := by
    rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hnodal : p = C p.leadingCoeff * Lagrange.nodal s id := by
    conv_lhs => rw [← hprod]
    rw [hroots, Lagrange.nodal]
    rfl
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hN : aeval shift (Lagrange.nodal s id) u = 0 := by
    have h := hu
    rw [hnodal, map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply] at h
    exact (smul_eq_zero.mp h).resolve_left hlc
  rcases s.eq_empty_or_nonempty with he | hne
  · refine ⟨0, fun n => ?_⟩
    have h1 : Lagrange.nodal s id = 1 := by rw [he]; simp [Lagrange.nodal]
    rw [h1, map_one, Module.End.one_apply] at hN
    rw [hN]
    simp
  · have hgeom : ∀ i ∈ s, ∀ n, aeval shift (Lagrange.basis s id i) u n =
        aeval shift (Lagrange.basis s id i) u 0 * i ^ n := by
      intro i hi
      have hstep : aeval shift (X - C i) (aeval shift (Lagrange.basis s id i) u) = 0 := by
        rw [← Module.End.mul_apply, ← map_mul, Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
          mul_left_comm]
        have hdvd := Lagrange.X_sub_C_dvd_nodal (s := s) id hi
        rw [id, EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero i) hdvd, map_mul,
          Module.End.mul_apply, hN, map_zero]
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h := congrFun hstep n
        rw [aeval_X_sub_C_apply] at h
        simp only [Pi.zero_apply] at h
        rw [pow_succ, ← mul_assoc, ← ih]
        linear_combination h
    refine ⟨fun i => aeval shift (Lagrange.basis s id i) u 0, fun n => ?_⟩
    have hsum := Lagrange.sum_basis (v := id) (Set.injOn_id _) hne
    have hu1 : u = aeval shift (∑ i ∈ s, Lagrange.basis s id i) u := by
      rw [hsum, map_one, Module.End.one_apply]
    calc u n = aeval shift (∑ i ∈ s, Lagrange.basis s id i) u n := by rw [← hu1]
      _ = ∑ i ∈ s, aeval shift (Lagrange.basis s id i) u n := by
          rw [map_sum, LinearMap.sum_apply, Finset.sum_apply]
      _ = ∑ i ∈ s, aeval shift (Lagrange.basis s id i) u 0 * i ^ n :=
          Finset.sum_congr rfl fun i hi => hgeom i hi n

open D5.S1.Recurrence.Algebraic.OEISA289916StrictIncrease (den num)
open D5.S1.Recurrence.OEISA400645 (squaredLimit r_quad r_bounds)
open D5.S0.Tower.NonPisotFrontier.BetaThirteen

/-- The characteristic polynomial `(X² - X + 1)(X⁴ - X³ - X² - X + 1)` of the recurrence
satisfied by the coefficients of Barker's generating function. -/
private def charPoly : ℂ[X] :=
  X ^ 6 - C 2 * X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - C 2 * X + 1

private theorem charPoly_natDegree : charPoly.natDegree = 6 := by
  unfold charPoly
  compute_degree!

private theorem charPoly_ne_zero : charPoly ≠ 0 := by
  intro h
  have := charPoly_natDegree
  rw [h, natDegree_zero] at this
  omega

private theorem aeval_charPoly (u : ℕ → ℂ) (j : ℕ) :
    aeval shift charPoly u j = u j - 2 * u (j + 1) + u (j + 2) - u (j + 3) + u (j + 4) -
      2 * u (j + 5) + u (j + 6) := by
  rw [aeval_apply, charPoly_natDegree]
  simp [Finset.sum_range_succ, charPoly, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  ring

/-- Coefficients of Barker's generating function satisfy the recurrence from index nine on. -/
private theorem rec_of_gf (v : ℕ → ℤ) (hv : PowerSeries.mk v * den = num) (j : ℕ) :
    v (j + 3) - 2 * v (j + 4) + v (j + 5) - v (j + 6) + v (j + 7) - 2 * v (j + 8) +
      v (j + 9) = 0 := by
  have hden : den = 1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 1 + PowerSeries.X ^ 2 -
      PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 - PowerSeries.X ^ 5 +
      PowerSeries.X ^ 6 := by
    unfold den
    ring
  have hnum : num = 1 + PowerSeries.X ^ 1 + PowerSeries.X ^ 7 + PowerSeries.X ^ 8 := by
    unfold num
    ring
  have h := congrArg (PowerSeries.coeff (j + 9)) hv
  rw [hden, hnum] at h
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub] at h
  simp [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_one] at h
  rw [PowerSeries.coeff_X] at h
  simp only [show j + 9 ≠ 1 by omega, ↓reduceIte] at h
  linarith

/-- `charPoly` factors through `y² - β y + 1`, `y² - (1 - β) y + 1` and `y² - y + 1`. -/
private theorem charPoly_eval (z : ℂ) :
    charPoly.eval z = (z ^ 2 - (betaThirteen : ℂ) * z + 1) *
      (z ^ 2 - (1 - (betaThirteen : ℂ)) * z + 1) * (z ^ 2 - z + 1) := by
  have hβ : (betaThirteen : ℂ) ^ 2 = betaThirteen + 3 := by exact_mod_cast betaThirteen_quadratic
  simp only [charPoly, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one]
  linear_combination (z ^ 2 * (z ^ 2 - z + 1)) * hβ

/-- Second-root parameter: the unit-circle pair is `t/2 ± i s`. -/
private def tt : ℝ := 1 - betaThirteen
private def ss : ℝ := Real.sqrt (1 - tt ^ 2 / 4)

private theorem bounds :
    2 < betaThirteen ∧ betaThirteen < 5 / 2 ∧ 17 / 10 < squaredLimit ∧ squaredLimit < 7 / 4 ∧
      squaredLimit * (betaThirteen - squaredLimit) = 1 := by
  have h2 := two_lt_betaThirteen
  have h3 : betaThirteen < 5 / 2 := by
    have := sqrt_thirteen_bounds.2
    simp only [betaThirteen]
    linarith
  have hr := r_bounds
  have hq := r_quad
  exact ⟨h2, h3, hr.1, hr.2, by linear_combination -hq⟩

private theorem ss_sq : ss ^ 2 = 1 - tt ^ 2 / 4 := by
  obtain ⟨h2, h3, -⟩ := bounds
  have : 0 ≤ 1 - tt ^ 2 / 4 := by simp only [tt]; nlinarith
  exact Real.sq_sqrt this

private theorem ss_pos : 0 < ss := by
  obtain ⟨h2, h3, -⟩ := bounds
  exact Real.sqrt_pos.mpr (by simp only [tt]; nlinarith)

/-- The six roots of `charPoly`. -/
private def roots6 : List ℂ :=
  [(squaredLimit : ℂ), ((betaThirteen - squaredLimit : ℝ) : ℂ), ⟨tt / 2, ss⟩, ⟨tt / 2, -ss⟩,
    ⟨1 / 2, Real.sqrt 3 / 2⟩, ⟨1 / 2, -(Real.sqrt 3 / 2)⟩]

private theorem roots6_isRoot : ∀ z ∈ roots6, charPoly.IsRoot z := by
  have hq : (squaredLimit : ℂ) ^ 2 - (betaThirteen : ℂ) * squaredLimit + 1 = 0 := by
    exact_mod_cast r_quad
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : ss ^ 2 = 1 - (1 - betaThirteen) ^ 2 / 4 := by simpa [tt] using ss_sq
  intro z hz
  rw [IsRoot, charPoly_eval]
  simp only [roots6, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hq]; ring
  · have : (((betaThirteen - squaredLimit : ℝ) : ℂ)) ^ 2 - (betaThirteen : ℂ) *
        ((betaThirteen - squaredLimit : ℝ) : ℂ) + 1 = 0 := by
      push_cast
      linear_combination hq
    rw [this]; ring
  · have : (⟨tt / 2, ss⟩ : ℂ) ^ 2 - (1 - (betaThirteen : ℂ)) * ⟨tt / 2, ss⟩ + 1 = 0 := by
      apply Complex.ext <;> simp [sq, tt] <;> nlinarith [hs]
    rw [this]; ring
  · have : (⟨tt / 2, -ss⟩ : ℂ) ^ 2 - (1 - (betaThirteen : ℂ)) * ⟨tt / 2, -ss⟩ + 1 = 0 := by
      apply Complex.ext <;> simp [sq, tt] <;> nlinarith [hs]
    rw [this]; ring
  · have : (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - ⟨1 / 2, Real.sqrt 3 / 2⟩ + 1 = 0 := by
      apply Complex.ext <;> simp [sq] <;> nlinarith [h3]
    rw [this]; ring
  · have : (⟨1 / 2, -(Real.sqrt 3 / 2)⟩ : ℂ) ^ 2 - ⟨1 / 2, -(Real.sqrt 3 / 2)⟩ + 1 = 0 := by
      apply Complex.ext <;> simp [sq] <;> nlinarith [h3]
    rw [this]; ring

end D5.S1.Recurrence.Algebraic.OEISA289916Asymptotics
