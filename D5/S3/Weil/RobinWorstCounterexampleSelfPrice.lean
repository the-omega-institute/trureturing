/- GID: D5/S3/Weil/RobinWorstCounterexampleSelfPrice
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A negative Robin-margin minimizer on an admissible set maximizes its self-priced resource objective. -/

import D5.S3.Arith.GoldenResourceOptimalInteger
import D5.S3.Weil.GronwallLowerEnvelope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false

namespace D5.S3.Weil.RobinWorstCounterexampleSelfPrice

open Filter Set
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.PaddingRatio
open D5.S3.Weil.GronwallLowerEnvelope

noncomputable section

/-- A strict Robin counterexample has a least margin on every admissible set, and
that least-margin state is optimal for the price determined by its own logarithmic
energy. -/
theorem robin_worst_counterexample_self_price
    {A : Set ℕ} (hA : ∀ n ∈ A, 5041 ≤ n)
    (hcounter : ∃ n ∈ A, robinLogMargin n < 0) :
    ∃ nstar ∈ A,
      robinLogMargin nstar < 0 ∧
        (∀ n ∈ A, robinLogMargin nstar ≤ robinLogMargin n) ∧
        (∀ n ∈ A,
          goldenResourceObjective
              (1 / (Real.log nstar * Real.log (Real.log nstar))) n ≤
            goldenResourceObjective
              (1 / (Real.log nstar * Real.log (Real.log nstar))) nstar) := by
  rcases hcounter with ⟨n₀, hn₀A, hn₀neg⟩
  have hbounded : IsBoundedUnder (· ≥ ·) atTop robinLogMargin := by
    have hlower : ∀ᶠ n : ℕ in atTop, (-1 : ℝ) ≤ robinLogMargin n := by
      obtain ⟨N, hN⟩ :=
        (gronwall_envelopes (Real.exp 1 - 1)
          (sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one))).1
      filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 5041] with n hnN hn5041
      have hpos : 0 < robinRatio n := by
        exact div_pos
          (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (by omega)))
          (mul_pos (mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (by omega)))
            (loglog_pos hn5041))
      have hratio : robinRatio n ≤ Real.exp 1 := by
        simpa only [robinRatio, add_sub_cancel] using hN n hnN
      rw [robin_log_margin_eq_neg_log hn5041]
      have hlog := (Real.log_le_iff_le_exp hpos).mpr hratio
      linarith only [hlog]
    exact isBoundedUnder_of_eventually_ge hlower
  have hev : ∀ᶠ n : ℕ in atTop, robinLogMargin n₀ < robinLogMargin n := by
    apply eventually_lt_of_lt_liminf _ hbounded
    rw [robin_log_margin_liminf]
    exact hn₀neg
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let S : Set ℕ := {n | robinLogMargin n ≤ robinLogMargin n₀} ∩ A
  have hSfinite : S.Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    have hnS : robinLogMargin n ≤ robinLogMargin n₀ := hn.1
    by_contra hnN
    have hNn : N ≤ n := le_of_not_gt hnN
    exact (not_lt_of_ge hnS) (hN n hNn)
  have hSnonempty : S.Nonempty := by
    refine ⟨n₀, ?_⟩
    change robinLogMargin n₀ ≤ robinLogMargin n₀ ∧ n₀ ∈ A
    exact ⟨le_rfl, hn₀A⟩
  obtain ⟨nstar, hnstarS, hminS⟩ :=
    Set.exists_min_image S robinLogMargin hSfinite hSnonempty
  have hnstarA : nstar ∈ A := hnstarS.2
  have hnstar5041 : 5041 ≤ nstar := hA nstar hnstarA
  have hstar_le_zero : robinLogMargin nstar ≤ robinLogMargin n₀ := hnstarS.1
  have hnstarneg : robinLogMargin nstar < 0 := hstar_le_zero.trans_lt hn₀neg
  have hminA : ∀ n ∈ A, robinLogMargin nstar ≤ robinLogMargin n := by
    intro n hnA'
    by_cases hnS : robinLogMargin n ≤ robinLogMargin n₀
    · exact hminS n ⟨hnS, hnA'⟩
    · exact hstar_le_zero.trans (lt_of_not_ge hnS).le
  refine ⟨nstar, hnstarA, hnstarneg, hminA, ?_⟩
  have log_gt_one : ∀ {m : ℕ}, 5041 ≤ m → 1 < Real.log (m : ℝ) := by
    intro m hm
    apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < m)).mpr
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3 ≤ m by omega))
  have hlogstar : 1 < Real.log (nstar : ℝ) := log_gt_one hnstar5041
  have hloglogstar : 0 < Real.log (Real.log (nstar : ℝ)) := Real.log_pos hlogstar
  let lambda : ℝ := 1 /
    (Real.log (nstar : ℝ) * Real.log (Real.log (nstar : ℝ)))
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact div_pos zero_lt_one
      (mul_pos (lt_trans zero_lt_one hlogstar) hloglogstar)
  have hmargin (m : ℕ) (hm : 5041 ≤ m) :
      robinLogMargin m =
        Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (m : ℝ))) -
          goldenResourceObjective 0 m := by
    rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ m)]
    simp only [zero_mul, sub_zero]
    rfl
  have hobj (m : ℕ) (hm : 5041 ≤ m) :
      goldenResourceObjective lambda m =
        goldenResourceObjective 0 m - lambda * Real.log (m : ℝ) := by
    rw [golden_resource_sigma_identity lambda (by omega : 1 ≤ m),
      golden_resource_sigma_identity 0 (by omega : 1 ≤ m)]
    ring
  have tangent : ∀ {x y : ℝ}, 1 < x → 1 < y →
      Real.log (Real.log y) ≤
        Real.log (Real.log x) + (1 / (x * Real.log x)) * (y - x) := by
    intro x y hx hy
    by_cases hxy : x = y
    · subst y
      simp
    have himage : Real.log '' Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := by
      rintro _ ⟨z, hz, rfl⟩
      exact Real.log_pos hz
    have hinner : StrictConcaveOn ℝ (Set.Ioi (1 : ℝ)) Real.log :=
      StrictConcaveOn.subset strictConcaveOn_log_Ioi
        (by intro z hz; change 1 < z at hz; change 0 < z; linarith)
        (convex_Ioi (1 : ℝ))
    have houter : StrictConcaveOn ℝ (Real.log '' Set.Ioi (1 : ℝ)) Real.log := by
      simpa only [Real.image_log_Ioi zero_lt_one, Real.log_one] using
        strictConcaveOn_log_Ioi
    have hmono : StrictMonoOn Real.log (Real.log '' Set.Ioi (1 : ℝ)) :=
      Real.strictMonoOn_log.mono himage
    have hsc : StrictConcaveOn ℝ (Set.Ioi (1 : ℝ))
        (fun z => Real.log (Real.log z)) :=
      houter.comp hinner hmono
        (Real.strictMonoOn_log.mono
          (by intro z hz; change 1 < z at hz; change 0 < z; linarith)).injOn
    have hd : HasDerivAt (fun z => Real.log (Real.log z))
        (1 / (x * Real.log x)) x := by
      convert (Real.hasDerivAt_log (ne_of_gt (lt_trans zero_lt_one hx))).log
          (Real.log_pos hx).ne' using 1
      field_simp
    have hstrict : Real.log (Real.log y) <
        Real.log (Real.log x) + (1 / (x * Real.log x)) * (y - x) := by
      rcases lt_or_gt_of_ne hxy with hxy' | hyx
      · have ht := hsc.slope_lt_of_hasDerivAt hx hy hxy' hd
        rw [slope_def_field] at ht
        have ht' := (div_lt_iff₀ (sub_pos.mpr hxy')).mp ht
        linarith
      · have ht := hsc.lt_slope_of_hasDerivAt hy hx hyx hd
        rw [slope_def_field] at ht
        have ht' := (lt_div_iff₀ (sub_pos.mpr hyx)).mp ht
        nlinarith
    exact hstrict.le
  intro n hnA'
  have hn5041 : 5041 ≤ n := hA n hnA'
  have hnlog : 1 < Real.log (n : ℝ) := log_gt_one hn5041
  have hΔ := hminA n hnA'
  have hΔstar := hmargin nstar hnstar5041
  have hΔn := hmargin n hn5041
  rw [hΔstar, hΔn] at hΔ
  have hobj0 : goldenResourceObjective 0 n ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (n : ℝ))) -
        robinLogMargin nstar := by
    rw [hΔstar]
    linarith
  have ht := tangent (x := Real.log (nstar : ℝ)) (y := Real.log (n : ℝ))
    hlogstar hnlog
  change goldenResourceObjective lambda n ≤ goldenResourceObjective lambda nstar
  rw [hobj n hn5041, hobj nstar hnstar5041]
  calc
    goldenResourceObjective 0 n - lambda * Real.log (n : ℝ) ≤
        (Real.eulerMascheroniConstant +
          Real.log (Real.log (Real.log (n : ℝ))) - robinLogMargin nstar) -
          lambda * Real.log (n : ℝ) := sub_le_sub_right hobj0 _
    _ ≤ (Real.eulerMascheroniConstant +
          Real.log (Real.log (Real.log (nstar : ℝ))) - robinLogMargin nstar) -
          lambda * Real.log (nstar : ℝ) := by
      dsimp [lambda]
      linarith
    _ = goldenResourceObjective 0 nstar - lambda * Real.log (nstar : ℝ) := by
      rw [hmargin nstar hnstar5041]
      ring

#print axioms robin_worst_counterexample_self_price

end
end D5.S3.Weil.RobinWorstCounterexampleSelfPrice
