/- GID: D5/S3/Weil/Scattering/FiniteScatteringCascade
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/FiniteScatteringCascade
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Half-integer shifted-xi scattering factors through a finite modular cascade. -/

import D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness
import D5.S3.Zeros.CompletedZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/- Library-search audit trail (2026-08-28):
   * Exact-name and body-shape searches for the shifted xi quotient and completed-zeta
     consecutive quotient found no matching D5 theorem or definition. The two frozen
     scattering theorems cover reflection, not a finite translation cascade.
   * Pinned Mathlib supplies `Finset.prod_range_div'` only on a commutative group and
     supplies no completed-zeta cascade theorem. The proof below therefore telescopes on
     a regular half-plane and uses the frozen meromorphic-normal-form uniqueness theorem.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Scattering.FiniteScatteringCascade

open Filter Set
open D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness
open D5.S3.Zeros.CompletedZeta

/-- The shifted entire-xi quotient from the source scattering family. -/
noncomputable def shiftedXiScattering (omega z : ℂ) : ℂ :=
  xiReading (1 / 2 - omega - Complex.I * z) /
    xiReading (1 / 2 + omega - Complex.I * z)

/-- The consecutive completed-zeta quotient in the modular scattering coefficient. -/
noncomputable def modularScatteringCoefficient (u : ℂ) : ℂ :=
  completedZetaReading (2 * u - 1) / completedZetaReading (2 * u)

private theorem completed_zeta_reading_meromorphic :
    MeromorphicOn completedZetaReading Set.univ := by
  have hzero : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ
  intro s _
  unfold completedZetaReading
  rw [show (fun w => completedRiemannZeta w) =
      (fun w => completedRiemannZeta₀ w - 1 / w - 1 / (1 - w)) by
    funext w
    exact completedRiemannZeta_eq w]
  exact (((hzero _ (Set.mem_univ _)).meromorphicAt.sub
    (by fun_prop)).sub (by fun_prop))

private theorem completed_zeta_reading_analyticAt_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) : AnalyticAt ℂ completedZetaReading s := by
  let rightHalfPlane : Set ℂ := {w | 1 < w.re}
  have hopen : IsOpen rightHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ completedZetaReading rightHalfPlane := by
    intro w hw
    change 1 < w.re at hw
    exact (differentiableAt_completedZeta
      (by
        intro h
        subst w
        norm_num at hw)
      (by
        intro h
        subst w
        norm_num at hw)).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hs)

private theorem completed_zeta_reading_ne_zero_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) : completedZetaReading s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  intro hCompleted
  apply riemannZeta_ne_zero_of_one_lt_re hs
  rw [riemannZeta_def_of_ne_zero hs0]
  change completedRiemannZeta s = 0 at hCompleted
  rw [hCompleted, zero_div]

private theorem prod_range_div_of_ne (f : ℕ → ℂ) (N : ℕ)
    (hne : ∀ j, j ≤ N → f j ≠ 0) :
    (∏ j ∈ Finset.range N, f j / f (j + 1)) = f 0 / f N := by
  induction N with
  | zero => simp [hne 0 (Nat.le_refl 0)]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih (fun j hj => hne j (hj.trans (Nat.le_succ N)))]
      field_simp [hne N (Nat.le_succ N), hne (N + 1) (Nat.le_refl _)]

private theorem finite_cascade_at (N : ℕ) (a : ℂ)
    (hLambda : ∀ j ∈ Finset.range (N + 1),
      completedZetaReading (a + (j : ℂ)) ≠ 0)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haN0 : a + N ≠ 0) (haN1 : a + N ≠ 1) :
    xiReading a / xiReading (a + N) =
      (a * (a - 1)) / ((a + N) * (a + N - 1)) *
        ∏ j ∈ Finset.range N,
          completedZetaReading (a + (j : ℂ)) /
            completedZetaReading (a + (j : ℂ) + 1) := by
  have hLambdaIndex (j : ℕ) (hj : j ≤ N) :
      completedZetaReading (a + (j : ℂ)) ≠ 0 := by
    exact hLambda j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  have hTelescoping :
      (∏ j ∈ Finset.range N,
          completedZetaReading (a + (j : ℂ)) /
            completedZetaReading (a + (j : ℂ) + 1)) =
        completedZetaReading a / completedZetaReading (a + N) := by
    simpa only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, add_assoc] using
      prod_range_div_of_ne
        (fun j => completedZetaReading (a + (j : ℂ))) N hLambdaIndex
  rw [xi_reading_eq_completed_zeta ha0 ha1,
    xi_reading_eq_completed_zeta haN0 haN1, hTelescoping]
  field_simp [hLambdaIndex 0 (Nat.zero_le N), hLambdaIndex N (Nat.le_refl N)]

private theorem shifted_xi_scattering_meromorphic (omega : ℂ) :
    MeromorphicOn (fun z => shiftedXiScattering omega z) Set.univ := by
  have hxi : AnalyticOnNhd ℂ xiReading Set.univ :=
    xi_reading_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  apply MeromorphicOn.div
  · intro z _
    exact (hxi _ (Set.mem_univ _)).comp (by fun_prop) |>.meromorphicAt
  · intro z _
    exact (hxi _ (Set.mem_univ _)).comp (by fun_prop) |>.meromorphicAt

private theorem finite_cascade_rhs_meromorphic (N : ℕ) :
    MeromorphicOn
      (fun z : ℂ =>
        let sz := 1 / 2 - Complex.I * z
        let a := sz - (N : ℂ) / 2
        (a * (a - 1)) / ((a + N) * (a + N - 1)) *
          ∏ j ∈ Finset.range N,
            modularScatteringCoefficient ((a + (j : ℂ) + 1) / 2))
      Set.univ := by
  apply MeromorphicOn.mul
  · intro z _
    fun_prop
  · apply MeromorphicOn.fun_prod
    intro j _ z _
    apply MeromorphicAt.div
    · exact (completed_zeta_reading_meromorphic _ (Set.mem_univ _)).comp_analyticAt
        (by fun_prop)
    · exact (completed_zeta_reading_meromorphic _ (Set.mem_univ _)).comp_analyticAt
        (by fun_prop)

/-- At a half-integer shift, the shifted-xi scattering quotient is the meromorphic
normal form of a finite cascade of consecutive completed-zeta quotients. -/
theorem finite_scattering_cascade (N : ℕ) :
    toMeromorphicNFOn
        (fun z => shiftedXiScattering ((N : ℂ) / 2) z) Set.univ =
      toMeromorphicNFOn
        (fun z : ℂ =>
          let sz := 1 / 2 - Complex.I * z
          let a := sz - (N : ℂ) / 2
          (a * (a - 1)) / ((a + N) * (a + N - 1)) *
            ∏ j ∈ Finset.range N,
              modularScatteringCoefficient ((a + (j : ℂ) + 1) / 2))
        Set.univ := by
  let regular : Set ℂ :=
    {z | 2 < (1 / 2 - Complex.I * z - (N : ℂ) / 2).re}
  have hregularOpen : IsOpen regular := by
    exact isOpen_lt continuous_const (by fun_prop)
  have hregularNonempty : regular.Nonempty := by
    refine ⟨Complex.I * ((N : ℂ) / 2 + 3), ?_⟩
    change 2 < (1 / 2 - Complex.I *
      (Complex.I * ((N : ℂ) / 2 + 3)) - (N : ℂ) / 2).re
    rw [show 1 / 2 - Complex.I * (Complex.I * ((N : ℂ) / 2 + 3)) -
        (N : ℂ) / 2 = 7 / 2 by
      rw [show Complex.I * (Complex.I * ((N : ℂ) / 2 + 3)) =
          -((N : ℂ) / 2 + 3) by
        rw [← mul_assoc, Complex.I_mul_I]
        simp]
      ring]
    norm_num
  funext target
  refine (meromorphic_continuation_unique isOpen_univ isPreconnected_univ
    hregularOpen hregularNonempty (Set.subset_univ regular)
    (meromorphicNFOn_toMeromorphicNFOn _ _)
    (meromorphicNFOn_toMeromorphicNFOn _ _) ?_) (Set.mem_univ target)
  intro z hz
  let a : ℂ := 1 / 2 - Complex.I * z - (N : ℂ) / 2
  have haRe : 2 < a.re := hz
  have hLambda (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
      completedZetaReading (a + (j : ℂ)) ≠ 0 := by
    apply completed_zeta_reading_ne_zero_of_one_lt_re
    simp only [Complex.add_re, Complex.natCast_re]
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have ha1 : a ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have haN0 : a + N ≠ 0 := by
    intro h
    have : (a + (N : ℂ)).re = 0 := by rw [h]; rfl
    simp only [Complex.add_re, Complex.natCast_re] at this
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have haN1 : a + N ≠ 1 := by
    intro h
    have : (a + (N : ℂ)).re = 1 := by rw [h]; rfl
    simp only [Complex.add_re, Complex.natCast_re] at this
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hpoint := finite_cascade_at N a hLambda ha0 ha1 haN0 haN1
  have hleftMeromorphic := shifted_xi_scattering_meromorphic ((N : ℂ) / 2)
  have hrightMeromorphic := finite_cascade_rhs_meromorphic N
  have hxi : AnalyticOnNhd ℂ xiReading Set.univ :=
    xi_reading_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hxiDenominator : xiReading (a + N) ≠ 0 := by
    rw [xi_reading_eq_completed_zeta haN0 haN1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) haN0)
      (sub_ne_zero.mpr haN1))
      (hLambda N (Finset.mem_range.mpr (Nat.lt_succ_self N)))
  have hleftAnalytic :
      AnalyticAt ℂ (fun z => shiftedXiScattering ((N : ℂ) / 2) z) z := by
    apply AnalyticAt.div
    · exact (hxi _ (Set.mem_univ _)).comp (by fun_prop)
    · exact (hxi _ (Set.mem_univ _)).comp (by fun_prop)
    · change xiReading (1 / 2 + (N : ℂ) / 2 - Complex.I * z) ≠ 0
      rw [show 1 / 2 + (N : ℂ) / 2 - Complex.I * z = a + N by
        dsimp only [a]
        ring]
      exact hxiDenominator
  have hrightAnalytic :
      AnalyticAt ℂ
        (fun z : ℂ =>
          let sz := 1 / 2 - Complex.I * z
          let a := sz - (N : ℂ) / 2
          (a * (a - 1)) / ((a + N) * (a + N - 1)) *
            ∏ j ∈ Finset.range N,
              modularScatteringCoefficient ((a + (j : ℂ) + 1) / 2)) z := by
    dsimp only [modularScatteringCoefficient]
    apply AnalyticAt.mul
    · apply AnalyticAt.div
      · fun_prop
      · fun_prop
      · change (a + N) * (a + N - 1) ≠ 0
        exact mul_ne_zero haN0 (sub_ne_zero.mpr haN1)
    · apply Finset.analyticAt_fun_prod
      intro j hj
      apply AnalyticAt.div
      · have hbase : 1 < (a + (j : ℂ)).re := by
          simp only [Complex.add_re, Complex.natCast_re]
          have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        have hsNumerator :
            1 < (2 * ((1 / 2 - Complex.I * z - (N : ℂ) / 2 +
              (j : ℂ) + 1) / 2) - 1).re := by
          convert hbase using 1
          dsimp only [a]
          ring
        have hinner : AnalyticAt ℂ
            (fun w : ℂ => 2 * ((1 / 2 - Complex.I * w - (N : ℂ) / 2 +
              (j : ℂ) + 1) / 2) - 1) z := by
          fun_prop
        exact AnalyticAt.comp
          (f := fun w : ℂ => 2 * ((1 / 2 - Complex.I * w - (N : ℂ) / 2 +
            (j : ℂ) + 1) / 2) - 1)
          (g := completedZetaReading)
          (completed_zeta_reading_analyticAt_of_one_lt_re hsNumerator) hinner
      · have hbase : 1 < (a + (j : ℂ) + 1).re := by
          simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
          have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        have hsDenominator :
            1 < (2 * ((1 / 2 - Complex.I * z - (N : ℂ) / 2 +
              (j : ℂ) + 1) / 2)).re := by
          convert hbase using 1
          dsimp only [a]
          ring
        have hinner : AnalyticAt ℂ
            (fun w : ℂ => 2 * ((1 / 2 - Complex.I * w - (N : ℂ) / 2 +
              (j : ℂ) + 1) / 2)) z := by
          fun_prop
        exact AnalyticAt.comp
          (f := fun w : ℂ => 2 * ((1 / 2 - Complex.I * w - (N : ℂ) / 2 +
            (j : ℂ) + 1) / 2))
          (g := completedZetaReading)
          (completed_zeta_reading_analyticAt_of_one_lt_re hsDenominator) hinner
      · have hden := hLambda (j + 1)
          (Finset.mem_range.mpr (Nat.succ_lt_succ (Finset.mem_range.mp hj)))
        rw [Nat.cast_add, Nat.cast_one] at hden
        convert hden using 1
        dsimp only [a]
        congr 1
        ring
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hleftMeromorphic (Set.mem_univ z),
    toMeromorphicNFAt_eq_self.2 hleftAnalytic.meromorphicNFAt,
    toMeromorphicNFOn_eq_toMeromorphicNFAt hrightMeromorphic (Set.mem_univ z),
    toMeromorphicNFAt_eq_self.2 hrightAnalytic.meromorphicNFAt]
  dsimp only [shiftedXiScattering, modularScatteringCoefficient]
  rw [show 1 / 2 - (N : ℂ) / 2 - Complex.I * z = a by
      dsimp only [a]
      ring,
    show 1 / 2 + (N : ℂ) / 2 - Complex.I * z = a + N by
      dsimp only [a]
      ring]
  convert hpoint using 1
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 2 <;> ring

#print axioms finite_scattering_cascade

end D5.S3.Weil.Scattering.FiniteScatteringCascade
