/- GID: D5/S3/CharacterSums/DirichletCyclicWindowZeroFree
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletCyclicWindowZeroFree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Long upper windows of the actual cyclic character family exclude zeta and L zeros. -/

import D5.S3.CharacterSums.DirichletCyclicContinuation
import Mathlib.NumberTheory.Chebyshev
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import D5.S3.Analytic.Laplace.LongWindowPoleExclusion

/-! # Zero exclusion from actual cyclic long windows

The window hypothesis is the only asymptotic premise. The analytic continuation,
actual pole orders, positive real residues, and moment estimates are proved for
the arithmetic family before applying the long-window contradiction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators
open D5.S3.CharacterSums.DirichletCyclicLaplace
open D5.S3.Analytic.Laplace.LongWindowBounds
open D5.S3.CharacterSums.DirichletCyclicContinuation
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.CharacterSums.DirichletRampEndpoint
open D5.S3.CharacterSums.DirichletRampLaplace
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)
open D5.S3.Analytic.Laplace.LongWindowPoleExclusion

namespace D5.S3.CharacterSums.DirichletCyclicWindowZeroFree

private theorem part_eq_finite {x : ℝ} (hx : 0 ≤ x) :
    mangoldtPart x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x := by
  rw [mangoldtPart_eq_range hx (Nat.lt_succ_floor x)]
  have hr : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp [mangoldtRamp]

private theorem character_exp_measurable {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Measurable (fun u : ℝ => characterRamp χ (Real.exp u)) := by
  have he (u : ℝ) : characterRamp χ (Real.exp u) =
      ∑' n : ℕ, (mangoldtRamp n (Real.exp u) : ℂ) * χ (n : ZMod N) := by
    simpa using (weighted_character_hasSum χ 0 u).tsum_eq.symm
  simp_rw [he]
  apply Measurable.tsum
  intro n
  exact ((Complex.continuous_ofReal.comp
    ((mangoldtRamp_continuous n).comp Real.continuous_exp)).mul continuous_const).measurable

/-- The actual log-coordinate signal is measurable at every point, not just almost everywhere. -/
private theorem gl1CyclicFamily_exp_measurable {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    Measurable (fun u : ℝ => gl1CyclicFamily (r := r) χ (Real.exp u)) := by
  have hm (j : Fin (r - 1)) :
      Measurable (fun u : ℝ => gChi (χ ^ (j.1 + 1)) (Real.exp u)) := by
    classical
    unfold gChi
    split_ifs
    · have he (u : ℝ) :
          (∑ n ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, mangoldtRamp n (Real.exp u)) =
            mangoldtPart (Real.exp u) := by
        exact (part_eq_finite (Real.exp_nonneg u)).symm
      simp_rw [he]
      have hp : Measurable (fun u : ℝ => mangoldtPart (Real.exp u)) := by
        unfold mangoldtPart
        apply Measurable.tsum
        intro n
        exact ((mangoldtRamp_continuous n).comp Real.continuous_exp).measurable
      fun_prop
    · exact (character_exp_measurable _).add (by fun_prop)
  unfold gl1CyclicFamily cyclicPositiveFamily
  exact U_exp_continuous.measurable.add (measurable_const.mul
    (Finset.measurable_sum _ fun j _ => Complex.measurable_re.comp (hm j)))

/-- Character twisting cannot increase the complete nonnegative arithmetic ramp. -/
private theorem characterRamp_norm_le {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 0 ≤ x) : ‖characterRamp χ x‖ ≤ mangoldtPart x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [characterRamp, mangoldtPart, mangoldtRamp]
  have h := normalized_ramp χ hxpos
  have heq := U_eq_complete_ramps hx
  unfold U at heq
  have he : mangoldtPart x = x *
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        Chebyshev.psi x := by linarith only [heq]
  rw [he]
  have hh := (div_le_iff₀ hxpos).mp h
  rw [sub_mul, div_mul_cancel₀ _ hxpos.ne'] at hh
  simpa only [mul_comm] using hh

/-- Chebyshev's linear bound gives a quadratic majorant without any zero assumptions. -/
private theorem mangoldtPart_le_square {x : ℝ} (hx : 0 ≤ x) :
    mangoldtPart x ≤ (Real.log 4 + 4) * x ^ 2 := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
      mangoldtRamp n x ≤ x * ArithmeticFunction.vonMangoldt n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n : ℝ) ≤ x :=
      (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2
    rw [ramp_eq_affine (Finset.mem_Ioc.mp hn).1 hnx]
    have hdiv : x / (n : ℝ) ≤ x :=
      (div_le_iff₀ hnpos).mpr (le_mul_of_one_le_right hx hn1)
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
  calc
    mangoldtPart x ≤ x * Chebyshev.psi x := by
      rw [part_eq_finite hx, Chebyshev.psi, Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ x * ((Real.log 4 + 4) * x) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hx) hx
    _ = _ := by ring

private theorem U_bound {x : ℝ} (hx : 1 ≤ x) :
    |U x| ≤ (Real.log 4 + 6 + |Real.eulerMascheroniConstant|) * x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hxsq : x ≤ x ^ 2 := by nlinarith
  have hp : 0 ≤ mangoldtPart x := tsum_nonneg fun n => mangoldtRamp_nonneg n x
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  rw [U_eq_complete_ramps hx0]
  calc
    |mangoldtPart x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x| ≤
        mangoldtPart x + x * Real.log x + |1 + Real.eulerMascheroniConstant| * x := by
      calc
        _ ≤ |mangoldtPart x - x * Real.log x| +
            |(1 + Real.eulerMascheroniConstant) * x| := abs_add_le _ _
        _ ≤ |mangoldtPart x| + |x * Real.log x| +
            |(1 + Real.eulerMascheroniConstant) * x| := by
          gcongr
          exact abs_sub (mangoldtPart x) (x * Real.log x)
        _ = _ := by rw [abs_of_nonneg hp, abs_mul, abs_mul, abs_of_nonneg hx0,
          abs_of_nonneg hlog0]
    _ ≤ (Real.log 4 + 4) * x ^ 2 + x ^ 2 +
        (1 + |Real.eulerMascheroniConstant|) * x ^ 2 := by
      gcongr
      · exact mangoldtPart_le_square hx0
      · nlinarith
      · simpa using (abs_add_le (1 : ℝ) Real.eulerMascheroniConstant)
    _ = _ := by ring

private theorem gChi_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖gChi χ x‖ ≤
      (Real.log 4 + 4 + ‖deriv χ.LFunction 1 / χ.LFunction 1‖) * x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hxsq : x ≤ x ^ 2 := by nlinarith
  simp only [gChi, ite_eq_right hχ]
  calc
    _ ≤ ‖characterRamp χ x‖ + ‖(x : ℂ) * (deriv χ.LFunction 1 / χ.LFunction 1)‖ :=
      norm_add_le _ _
    _ ≤ (Real.log 4 + 4) * x ^ 2 +
        x * ‖deriv χ.LFunction 1 / χ.LFunction 1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0]
      exact add_le_add_left ((characterRamp_norm_le χ hx0).trans
        (mangoldtPart_le_square hx0)) _
    _ ≤ _ := by nlinarith [norm_nonneg (deriv χ.LFunction 1 / χ.LFunction 1)]

/-- A zero-independent bound for the actual cyclic family in logarithmic coordinates. -/
private theorem gl1CyclicFamily_exp_growth {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 ≤ u →
      |gl1CyclicFamily (r := r) χ (Real.exp u)| ≤ M * Real.exp (2 * u) := by
  let B := Real.log 4 + 6 + |Real.eulerMascheroniConstant|
  let a : ℝ := 1 / (3 * r + 1 : ℝ)
  let b : Fin (r - 1) → ℝ := fun j =>
    max B (Real.log 4 + 4 +
      ‖deriv (χ ^ (j.1 + 1)).LFunction 1 / (χ ^ (j.1 + 1)).LFunction 1‖)
  refine ⟨B + a * ∑ j, b j, ?_, ?_⟩
  · dsimp [B, a, b]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  intro u hu
  have hx : 1 ≤ Real.exp u := Real.one_le_exp hu
  have hj (j : Fin (r - 1)) :
      ‖gChi (χ ^ (j.1 + 1)) (Real.exp u)‖ ≤ b j * Real.exp u ^ 2 := by
    by_cases hp : χ ^ (j.1 + 1) = 1
    · rw [hp]
      have heq : gChi (1 : DirichletCharacter ℂ N) (Real.exp u) = (U (Real.exp u) : ℂ) := by
        rw [gChi, ite_eq_left rfl]
        rw [← part_eq_finite (Real.exp_nonneg u), U_eq_complete_ramps (Real.exp_nonneg u)]
        congr 1
        ring
      rw [heq]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (U_bound hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    · exact (gChi_bound _ hp hx).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  have hs : |∑ j : Fin (r - 1), (gChi (χ ^ (j.1 + 1)) (Real.exp u)).re| ≤
      (∑ j, b j) * Real.exp u ^ 2 := by
    calc
      _ ≤ ∑ j : Fin (r - 1), |(gChi (χ ^ (j.1 + 1)) (Real.exp u)).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, b j * Real.exp u ^ 2 := Finset.sum_le_sum fun j _ =>
        (Complex.abs_re_le_norm _).trans (hj j)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have ha : 0 ≤ a := by dsimp [a]; positivity
  change |U (Real.exp u) + a * _| ≤ _
  calc
    _ ≤ |U (Real.exp u)| + |a * _| := abs_add_le _ _
    _ = |U (Real.exp u)| + a * |∑ j : Fin (r - 1),
        (gChi (χ ^ (j.1 + 1)) (Real.exp u)).re| := by rw [abs_mul, abs_of_nonneg ha]
    _ ≤ B * Real.exp u ^ 2 + a * ((∑ j, b j) * Real.exp u ^ 2) :=
      add_le_add (U_bound hx) (mul_le_mul_of_nonneg_left hs ha)
    _ = _ := by rw [show Real.exp (2 * u) = Real.exp u ^ 2 by
        rw [two_mul, Real.exp_add, pow_two]]; ring


private theorem logarithmic_windows {G : ℝ → ℝ} {θ δ C : ℝ}
    (hw : LongWindowUpperBound G θ δ C) :
    ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), G (Real.exp u) ≤ C * Real.exp (θ * u) := by
  intro U₀
  obtain ⟨Y, hY, hY0, hbound⟩ := hw.2 (Real.exp U₀)
  refine ⟨Real.log Y, ?_, ?_⟩
  · exact (Real.le_log_iff_exp_le hY0).mpr hY
  · intro u hu
    have hx : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      constructor
      · rw [← Real.exp_log hY0]
        exact Real.exp_le_exp.mpr hu.1
      · rw [Real.rpow_def_of_pos hY0]
        apply Real.exp_le_exp.mpr
        linarith [hu.2]
    have hb := hbound (Real.exp u) hx
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp] at hb
    simpa only [mul_comm u θ] using hb

private theorem actual_zero_exclusion {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) {θ δ C : ℝ}
    (hθ : 0 ≤ θ) (hw : LongWindowUpperBound (gl1CyclicFamily (r := r) χ) θ δ C) :
    ∀ z ∈ actualZeros (r := r) χ, ¬ θ < z.re := by
  let g : ℝ → ℝ := fun u => gl1CyclicFamily (r := r) χ (Real.exp u)
  let F : ℂ → ℂ := continuation (r := r) χ
  let Z : Set ℂ := actualZeros (r := r) χ
  let residue : ℂ → ℂ := fun z =>
    (-1 / (z * (z - 1))) *
      ((∑ i, factorWeight r i * analyticOrderNatAt (analyticFactor χ i) z : ℝ) : ℂ)
  obtain ⟨M, _, hM⟩ := gl1CyclicFamily_exp_growth χ
  have hp := continuation_actual_poles χ hr
  apply long_window_pole_exclusion (g := g) (F := F) (Z := Z) (residue := residue)
    (M := M) (C := C) (gl1CyclicFamily_exp_measurable χ) hM
  · intro z hz
    dsimp only [laplace, g, F]
    rw [integral_Ici_eq_integral_Ioi]
    simpa only [mul_comm] using continuation_half_plane_laplace χ hr (by linarith : 1 < z.re)
  · intro z hz
    exact (actualZeros_re_lt_one χ hr hz).le
  · intro z _
    exact hp.2.1 z
  · exact hp.1
  · intro z hz
    exact (hp.2.2 z hz).2.2.1
  · intro z hz
    exact (hp.2.2 z hz).2.1
  · intro β hβ
    exact (actual_real_residue_pos χ hr hβ (by simp)).1
  · exact hθ
  · exact hw.1
  · exact logarithmic_windows hw


/-- Long upper windows of the actual cyclic family exclude both zeta zeros
and all nontrivial powers' Dirichlet L zeros to the right of their exponent.
The assertion also holds for the principal character with its order-one family. -/
theorem gl1_long_window_zero_free {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {θ δ C : ℝ}
    (hw : 0 < δ ∧
      ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 0 < Y ∧
        ∀ x ∈ Icc Y (Y ^ (1 + δ)),
          gl1CyclicFamily (r := orderOf χ) χ x ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re →
      riemannZeta s ≠ 0 ∧
        ∀ j : ℕ, 1 ≤ j → j < orderOf χ → (χ ^ j).LFunction s ≠ 0 := by
  by_cases hθ : 0 < θ
  · have hfree := actual_zero_exclusion χ le_rfl hθ.le hw
    intro s hs
    have hs0 : 0 < s.re := hθ.trans hs
    constructor
    · intro hz
      exact hfree s (zeta_zero_mem_actualZeros χ hs0 hz) hs
    · intro j hj hjr hzero
      let i : Fin (orderOf χ - 1) := ⟨j - 1, by omega⟩
      have hi : i.1 + 1 = j := by dsimp [i]; omega
      apply hfree s (member_zero_mem_actualZeros χ hs0 i ?_) hs
      simpa only [hi] using hzero
  · exfalso
    let ρ := zetaZeroData.zero 0
    have hρ := zetaZeroData_isNontrivial 0
    have hρpos : 0 < ρ.re := hρ.2.1
    let ε := ρ.re / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hθε : θ ≤ ε := le_trans (le_of_not_gt hθ) hε.le
    have hwε : LongWindowUpperBound
        (gl1CyclicFamily (r := orderOf χ) χ) ε δ |C| := by
      refine ⟨hw.1, fun Y₀ => ?_⟩
      obtain ⟨Y, hY, hYpos, hb⟩ := hw.2 (max Y₀ 1)
      refine ⟨Y, (le_max_left _ _).trans hY, hYpos, fun x hx => (hb x hx).trans ?_⟩
      have hx1 : 1 ≤ x := ((le_max_right _ _).trans hY).trans hx.1
      exact mul_le_mul (le_abs_self C)
        (Real.rpow_le_rpow_of_exponent_le hx1 hθε)
        (Real.rpow_nonneg (by linarith) _) (abs_nonneg C)
    have hfree := actual_zero_exclusion χ le_rfl hε.le hwε
    apply hfree ρ (zeta_zero_mem_actualZeros χ hρpos hρ.1)
    dsimp [ε]
    linarith

/-- Windows for every exponent above one half exclude all zeros strictly
to the right of the critical line in the actual cyclic family. -/
theorem gl1_zero_free_at_half_of_all_windows {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hw : ∀ θ : ℝ, (1 : ℝ) / 2 < θ → θ < 1 → ∃ δ C : ℝ,
      0 < δ ∧
        ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 0 < Y ∧
          ∀ x ∈ Icc Y (Y ^ (1 + δ)),
            gl1CyclicFamily (r := orderOf χ) χ x ≤ C * x ^ θ) :
    ∀ s : ℂ, (1 : ℝ) / 2 < s.re →
      riemannZeta s ≠ 0 ∧
        ∀ j : ℕ, 1 ≤ j → j < orderOf χ → (χ ^ j).LFunction s ≠ 0 := by
  intro s hs
  let θ : ℝ := ((1 : ℝ) / 2 + min s.re 1) / 2
  have hmin : (1 : ℝ) / 2 < min s.re 1 := lt_min hs (by norm_num)
  have hθ : (1 : ℝ) / 2 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith [min_le_right s.re 1]
  have hθs : θ < s.re := by dsimp [θ]; linarith [min_le_left s.re 1]
  obtain ⟨δ, C, hW⟩ := hw θ hθ hθ1
  exact gl1_long_window_zero_free χ hW s hθs


end D5.S3.CharacterSums.DirichletCyclicWindowZeroFree
