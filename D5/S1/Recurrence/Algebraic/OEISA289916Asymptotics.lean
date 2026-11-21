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

private theorem roots6_nodup : roots6.Nodup := by
  obtain ⟨h2, h3, hr1, hr2, hprod⟩ := bounds
  have hs := ss_pos
  have h3p : 0 < Real.sqrt 3 := by positivity
  have hbr : 4 / 7 < betaThirteen - squaredLimit := by nlinarith
  simp only [roots6, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  repeat' apply And.intro
  all_goals
    intro h
    first
    | exact h.elim
    | have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp [tt] at hre him
      all_goals nlinarith

private theorem charPoly_roots : charPoly.roots = roots6.toFinset.val := by
  have hle : roots6.toFinset.val ≤ charPoly.roots :=
    (Multiset.le_iff_subset (Finset.nodup _)).mpr fun z hz =>
      (mem_roots charPoly_ne_zero).mpr (roots6_isRoot z (List.mem_toFinset.mp hz))
  have hcard : Multiset.card charPoly.roots ≤ Multiset.card roots6.toFinset.val := by
    rw [Finset.card_val, List.toFinset_card_of_nodup roots6_nodup]
    calc Multiset.card charPoly.roots ≤ charPoly.natDegree := card_roots' charPoly
      _ = 6 := charPoly_natDegree
      _ = roots6.length := rfl
  exact (Multiset.eq_of_le_of_card_le hle hcard).symm

private theorem roots6_norm : ∀ z ∈ roots6, z ≠ (squaredLimit : ℂ) → ‖z‖ ≤ 1 := by
  obtain ⟨h2, h3, hr1, hr2, hprod⟩ := bounds
  have hs : ss ^ 2 = 1 - (1 - betaThirteen) ^ 2 / 4 := by simpa [tt] using ss_sq
  have h3s : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  intro z hz hne
  rw [Complex.norm_def, Real.sqrt_le_one]
  simp only [roots6, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · rw [Complex.normSq_ofReal]
    nlinarith
  all_goals
    rw [Complex.normSq_apply]
    simp [tt]
    nlinarith

/-- Coefficients of Barker's generating function for A289916 grow like `D r^n` with bounded
error and `D > 0`, and their consecutive ratios tend to `r`, where `r` is the largest real root
of `y⁴ - y³ - y² - y + 1`. -/
theorem result :
    ∀ v : ℕ → ℤ, PowerSeries.mk v * den = num → ∃ D : ℝ, 0 < D ∧
      (fun n => (v n : ℝ) - D * squaredLimit ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
      Tendsto (fun n => (v (n + 1) : ℝ) / v n) atTop (nhds squaredLimit) := by
  intro v hv
  obtain ⟨-, -, hr1, hr2, -⟩ := bounds
  have hr0 : 0 < squaredLimit := by linarith
  -- the shifted sequence is annihilated by `charPoly`
  set u : ℕ → ℂ := fun j => ((v (j + 3) : ℤ) : ℂ) with hudef
  have hu : aeval shift charPoly u = 0 := by
    funext j
    rw [aeval_charPoly]
    have h := rec_of_gf v hv j
    simp only [hudef, Pi.zero_apply, show j + 1 + 3 = j + 4 by omega,
      show j + 2 + 3 = j + 5 by omega, show j + 3 + 3 = j + 6 by omega,
      show j + 4 + 3 = j + 7 by omega, show j + 5 + 3 = j + 8 by omega,
      show j + 6 + 3 = j + 9 by omega]
    exact_mod_cast h
  have hnd : charPoly.roots.Nodup := by rw [charPoly_roots]; exact Finset.nodup _
  obtain ⟨α, hα⟩ := geom_decomp charPoly charPoly_ne_zero hnd u hu
  rw [charPoly_roots, Finset.val_toFinset] at hα
  set S := roots6.toFinset with hS
  have hrS : (squaredLimit : ℂ) ∈ S := by simp [hS, roots6]
  set K : ℝ := ∑ z ∈ S.erase (squaredLimit : ℂ), ‖α z‖ with hK
  set A : ℝ := (α (squaredLimit : ℂ)).re with hA
  -- `v (n + 3) - A r^n` is bounded by `K`
  have hbound : ∀ n, |(v (n + 3) : ℝ) - A * squaredLimit ^ n| ≤ K := by
    intro n
    have hsplit := Finset.add_sum_erase S (fun z => α z * z ^ n) hrS
    have hdiff : u n - α (squaredLimit : ℂ) * (squaredLimit : ℂ) ^ n =
        ∑ z ∈ S.erase (squaredLimit : ℂ), α z * z ^ n := by
      rw [hα n, ← hsplit]
      ring
    have hnorm : ‖u n - α (squaredLimit : ℂ) * (squaredLimit : ℂ) ^ n‖ ≤ K := by
      rw [hdiff]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
      have hz1 := Finset.ne_of_mem_erase hz
      have hz2 := List.mem_toFinset.mp (Finset.mem_of_mem_erase hz)
      have hzn := roots6_norm z hz2 hz1
      rw [norm_mul, norm_pow]
      calc ‖α z‖ * ‖z‖ ^ n ≤ ‖α z‖ * 1 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg z) hzn
        _ = ‖α z‖ := mul_one _
    have hre : (u n - α (squaredLimit : ℂ) * (squaredLimit : ℂ) ^ n).re =
        (v (n + 3) : ℝ) - A * squaredLimit ^ n := by
      simp [hudef, hA, Complex.mul_re]
      rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [← hre]
    exact (Complex.abs_re_le_norm _).trans hnorm
  set D : ℝ := A / squaredLimit ^ 3 with hD
  have hdev : ∀ n, 3 ≤ n → |(v n : ℝ) - D * squaredLimit ^ n| ≤ K := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h := hbound m
    have : D * squaredLimit ^ (m + 3) = A * squaredLimit ^ m := by
      rw [hD, pow_add]
      field_simp
    rwa [this]
  have hbig : (fun n => (v n : ℝ) - D * squaredLimit ^ n) =O[atTop] (fun _ => (1 : ℝ)) :=
    IsBigO.of_bound K (eventually_atTop.mpr ⟨3, fun n hn => by
      rw [Real.norm_eq_abs, norm_one, mul_one]
      exact hdev n hn⟩)
  -- strict increase forces `D > 0`
  have hinc := (D5.S1.Recurrence.Algebraic.OEISA289916StrictIncrease.result).2 v hv
  have hgrow : ∀ n, (v 0 : ℝ) + n ≤ v n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hinc n
      have : (v n : ℝ) + 1 ≤ v (n + 1) := by exact_mod_cast this
      push_cast
      linarith
  have hDpos : 0 < D := by
    by_contra hD0
    push Not at hD0
    obtain ⟨n, hn⟩ : ∃ n : ℕ, K - v 0 < n ∧ 3 ≤ n := by
      refine ⟨⌈K - (v 0 : ℝ)⌉₊ + 3, ?_, by omega⟩
      have := Nat.le_ceil (K - (v 0 : ℝ))
      push_cast
      linarith
    have h1 := hgrow n
    have h2 := (abs_le.mp (hdev n hn.2)).2
    have h3 : D * squaredLimit ^ n ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hD0 (pow_nonneg hr0.le n)
    linarith [hn.1]
  refine ⟨D, hDpos, hbig, ?_⟩
  -- the ratio limit
  have hpow : Tendsto (fun n : ℕ => squaredLimit ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  have hinv : Tendsto (fun n : ℕ => (squaredLimit ^ n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have he : Tendsto (fun n => ((v n : ℝ) - D * squaredLimit ^ n) * (squaredLimit ^ n)⁻¹)
      atTop (nhds 0) := by
    have h := hbig.mul (isBigO_refl (fun n : ℕ => (squaredLimit ^ n)⁻¹) atTop)
    simp only [one_mul] at h
    exact h.trans_tendsto hinv
  have hden : Tendsto (fun n => (v n : ℝ) / squaredLimit ^ n) atTop (nhds D) := by
    have h := he.add_const D
    rw [zero_add] at h
    refine h.congr fun n => ?_
    have : squaredLimit ^ n ≠ 0 := pow_ne_zero n hr0.ne'
    field_simp
    ring
  have hnum : Tendsto (fun n => (v (n + 1) : ℝ) / squaredLimit ^ n) atTop
      (nhds (squaredLimit * D)) := by
    have h := (hden.comp (tendsto_add_atTop_nat 1)).const_mul squaredLimit
    refine h.congr fun n => ?_
    have : squaredLimit ^ n ≠ 0 := pow_ne_zero n hr0.ne'
    simp only [Function.comp_apply, pow_succ]
    field_simp
  have h := hnum.div hden hDpos.ne'
  rw [mul_div_assoc, div_self hDpos.ne', mul_one] at h
  refine h.congr fun n => ?_
  have : squaredLimit ^ n ≠ 0 := pow_ne_zero n hr0.ne'
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ this]

end D5.S1.Recurrence.Algebraic.OEISA289916Asymptotics
