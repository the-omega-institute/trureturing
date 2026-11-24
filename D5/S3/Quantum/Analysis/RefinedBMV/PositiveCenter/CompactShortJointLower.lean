/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortJointLower
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quartic lower bound for the undifferentiated short-gap joint moment. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMoments
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalQuadrature
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.HalfGapSlope
import D5.S3.Quantum.Recovery.BKMSpectralVariance
import D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A fourth-order lower bound for the undifferentiated midpoint moment. -/

namespace RefinedBMV.PositiveCenter

open scoped BigOperators

noncomputable section

open private shortJointAverage_add shortJointAverage_mul shortJointAverage_le
  shortJointAverage_swap from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMidpoint
open private cosh_quartic_lower from D5.S3.Quantum.Recovery.BKMSpectralVariance
open private shortMidpointMoment_eq_gridAverage from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure
open private gridAverage gridPoint from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
open private compactMixedT_eq_cutoff from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison
open private quadratureTailTerm from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalQuadrature

/-- The lower fourth-order approximation at center `s` and gap `d`. -/
def shortJointMomentFourth (p : ℕ) (s d : ℝ) : ℝ :=
  shortMidpointMoment p 0 0 s + ((d / 2) ^ 2 / 2) * shortMidpointMoment p 1 0 s +
    ((d / 2) ^ 4 / 24) * shortMidpointMoment p 2 0 s

/-- Symmetry in the two gaps gives the quartic lower bound for the joint moment. -/
theorem shortJointMomentFourth_le (p : ℕ) (u v : ℝ) :
    shortJointMomentFourth p ((u + v) / 2) (v - u) ≤ 1 + compositionMoment p u v := by
  rw [add_comm 1 (compositionMoment p u v), compositionMoment, sub_add_cancel]
  let s := (u + v) / 2
  let q := (v - u) / 2
  let F (x y : ℝ) := Real.exp (x * u + y * v)
  change shortJointMomentFourth p s (v - u) ≤ shortJointAverage p F
  have hpair (x y : ℝ) : Real.exp (s * (x + y)) * Real.cosh (q * (y - x)) =
      (1 / 2) * (F x y + F y x) := by
    have hx : x * u + y * v = s * (x + y) + q * (y - x) := by
      dsimp only [s, q]
      ring
    have hy : y * u + x * v = s * (x + y) + -(q * (y - x)) := by
      dsimp only [s, q]
      ring
    dsimp only [F]
    rw [hx, hy]
    simp only [Real.cosh_eq, Real.exp_add]
    ring
  have havg : shortJointAverage p (fun x y ↦
      Real.exp (s * (x + y)) * Real.cosh (q * (y - x))) = shortJointAverage p F := by
    simp_rw [hpair]
    rw [shortJointAverage_mul, shortJointAverage_add, shortJointAverage_swap p F]
    ring
  have hpoly (x y : ℝ) :
      Real.exp (s * (x + y)) * (1 + (q * (y - x)) ^ 2 / 2 + (q * (y - x)) ^ 4 / 24) =
        shortMidpointMonomial s 0 0 x y + (q ^ 2 / 2) * shortMidpointMonomial s 1 0 x y +
          (q ^ 4 / 24) * shortMidpointMonomial s 2 0 x y := by
    norm_num [shortMidpointMonomial] <;> ring
  have hfourth : shortJointAverage p (fun x y ↦
      Real.exp (s * (x + y)) * (1 + (q * (y - x)) ^ 2 / 2 + (q * (y - x)) ^ 4 / 24)) =
        shortJointMomentFourth p s (v - u) := by
    simp_rw [hpoly, shortJointAverage_add, shortJointAverage_mul] <;> rfl
  rw [← hfourth, ← havg]
  exact shortJointAverage_le p fun _ _ ↦
    mul_le_mul_of_nonneg_left (cosh_quartic_lower _) (Real.exp_pos _).le

/-- The polynomial obtained by averaging the quartic over the conditional separation. -/
def shortJointFourthPolynomial (h d r : ℝ) : ℝ :=
  1 + d ^ 2 * r * (r + 2 * h) / 24 +
    d ^ 4 * r * (r + 2 * h) * (3 * r ^ 2 + 6 * h * r - 4 * h ^ 2) / 5760

-- The coefficients of the polynomial factor in the quadrature integrand, in increasing order.
private def shortJointFourthCoeff (h d : ℝ) : ℕ → ℝ
  | 0 => h
  | 1 => 1 + d ^ 2 * h ^ 2 / 12 - d ^ 4 * h ^ 4 / 720
  | 2 => h * d ^ 2 / 8
  | 3 => d ^ 2 / 24 + d ^ 4 * h ^ 2 / 288
  | 4 => h * d ^ 4 / 384
  | 5 => d ^ 4 / 1920
  | _ => 0

/-- The joint quadrature integrand is smooth in the spatial variable. -/
theorem shortJointFourthIntegrand_contDiff (h d s : ℝ) :
    ContDiff ℝ ⊤ (fun r : ℝ ↦ (r + h) * shortJointFourthPolynomial h d r * Real.exp (s * r)) := by
  unfold shortJointFourthPolynomial
  fun_prop

/-- Every spatial derivative of the joint quadrature integrand is nonnegative on the
nonnegative half-line for the short-gap quadrature parameters. -/
theorem shortJointFourthIntegrand_iteratedDeriv_nonneg (j : ℕ) {h d s r : ℝ}
    (hh₀ : 0 ≤ h) (hh₁ : h ≤ 3 / 11) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1)
    (hs : 0 ≤ s) (hr : 0 ≤ r) :
    0 ≤ iteratedDeriv j
      (fun x : ℝ ↦ (x + h) * shortJointFourthPolynomial h d x * Real.exp (s * x)) r := by
  have hdh : d * h ≤ 1 := calc
    d * h ≤ 1 * h := mul_le_mul_of_nonneg_right hd₁ hh₀
    _ = h := one_mul h
    _ ≤ 1 := hh₁.trans (by norm_num)
  have hfourth : d ^ 4 * h ^ 4 ≤ 1 := by
    simpa only [mul_pow, one_pow] using pow_le_pow_left₀ (mul_nonneg hd₀ hh₀) hdh 4
  have hsquare : 0 ≤ d ^ 2 * h ^ 2 := by positivity
  have hlinear : 0 ≤ 1 + d ^ 2 * h ^ 2 / 12 - d ^ 4 * h ^ 4 / 720 := by
    linarith only [hfourth, hsquare]
  have hcoeff (k : ℕ) (hk : k ∈ Finset.range 6) : 0 ≤ shortJointFourthCoeff h d k := by
    have hk' : k < 6 := Finset.mem_range.mp hk
    interval_cases k <;> simp only [shortJointFourthCoeff]
    all_goals first | exact hlinear | positivity
  let f (k : ℕ) (x : ℝ) := shortJointFourthCoeff h d k * (x ^ k * Real.exp (s * x))
  have hexpand :
      (fun x : ℝ ↦ (x + h) * shortJointFourthPolynomial h d x * Real.exp (s * x)) =
        (fun x : ℝ ↦ ∑ k ∈ Finset.range 6, f k x) := by
    funext x
    norm_num [Finset.sum_range_succ, f, shortJointFourthCoeff, shortJointFourthPolynomial] <;> ring
  have hdiff (k : ℕ) : ContDiffAt ℝ j (f k) r := by
    dsimp only [f]
    fun_prop
  rw [hexpand, iteratedDeriv_fun_sum (f := f) (I := Finset.range 6) (fun k _ ↦ hdiff k)]
  refine Finset.sum_nonneg fun k hk ↦ ?_
  change 0 ≤ iteratedDeriv j
    (fun x : ℝ ↦ shortJointFourthCoeff h d k * (x ^ k * Real.exp (s * x))) r
  rw [iteratedDeriv_const_mul_field (shortJointFourthCoeff h d k)
    (fun x : ℝ ↦ x ^ k * Real.exp (s * x))]
  refine mul_nonneg (hcoeff k hk) ?_
  have hpow : ContDiffAt ℝ j (fun x : ℝ ↦ x ^ k) r := by fun_prop
  have hexp : ContDiffAt ℝ j (fun x : ℝ ↦ Real.exp (s * x)) r := by fun_prop
  rw [iteratedDeriv_fun_mul hpow hexp]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [iteratedDeriv_pow, iteratedDeriv_exp_const_mul]
  positivity

/-- The quartic lower approximation as a single sum on the reflected marginal grid. -/
theorem shortJointMomentFourth_eq_gridSum {p : ℕ} (hp : 0 < p) (s d : ℝ) :
    let h := 3 / (p : ℝ)
    shortJointMomentFourth p s d =
      (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) *
        (h * ∑ n ∈ Finset.range (p + 1),
          let r := h * n
          (r + h) * shortJointFourthPolynomial h d r * Real.exp (s * r)) := by
  intro h
  let P := shortJointFourthPolynomial h d
  let W (j : Fin 4) (z : ℝ) :=
    shortConditionalEvenWeight j h (2 + h - z) * Real.exp (-z * s)
  have hm (j : Fin 4) : shortMidpointMoment p j 0 s = gridAverage p (W j) := by
    simpa only [W, h, pow_zero, mul_one] using shortMidpointMoment_eq_gridAverage hp j 0 s
  have hgrid : shortJointMomentFourth p s d =
      gridAverage p (fun z ↦ P (2 - z) * Real.exp (-z * s)) := by
    unfold shortJointMomentFourth
    change shortMidpointMoment p ((0 : Fin 4) : ℕ) 0 s +
      ((d / 2) ^ 2 / 2) * shortMidpointMoment p ((1 : Fin 4) : ℕ) 0 s +
      ((d / 2) ^ 4 / 24) * shortMidpointMoment p ((2 : Fin 4) : ℕ) 0 s = _
    rw [hm 0, hm 1, hm 2]
    unfold gridAverage
    simp only [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    norm_num [W, P, shortJointFourthPolynomial, shortConditionalEvenWeight] <;> ring
  rw [hgrid]
  let D : ℝ := (DimThree.gaps p).length
  let F (r : ℝ) := (r + h) * P r * Real.exp (s * r)
  let G (i : ℕ) := (↑(p + 1 - i) : ℝ) *
    (P (2 - gridPoint p i) * Real.exp (-(gridPoint p i) * s))
  have hh : 0 < h := by dsimp only [h]; positivity
  have hscale : h * (p : ℝ) = 3 := by
    dsimp only [h]
    exact div_mul_cancel₀ _ (by exact_mod_cast hp.ne')
  have hsum : (∑ i ∈ Finset.range (p + 1), G i) =
      (Real.exp (-2 * s) / h) * ∑ n ∈ Finset.range (p + 1), F (h * n) := by
    rw [← Finset.sum_range_reflect G (p + 1), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hindex : p + 1 - 1 - n = p - n := by omega
    have hmult : p + 1 - (p - n) = n + 1 := by omega
    have hz : gridPoint p (p - n) = 2 - h * n := by
      change h * ((p - n : ℕ) : ℝ) - 1 = _
      rw [Nat.cast_sub hn']
      linear_combination hscale
    rw [hindex]
    dsimp only [G, F]
    rw [hmult, hz, Nat.cast_add, Nat.cast_one,
      show 2 - (2 - h * (n : ℝ)) = h * n by ring,
      show -(2 - h * (n : ℝ)) * s = -2 * s + s * (h * n) by ring,
      Real.exp_add]
    field_simp [hh.ne'] <;> ring
  change (∑ i ∈ Finset.range (p + 1), G i) / D =
    (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) *
      (h * ∑ n ∈ Finset.range (p + 1), F (h * n))
  have hcountNat : 2 * (DimThree.gaps p).length = (p + 1) * (p + 2) := by
    rw [DimThree.gaps_length_eq_choose, Nat.mul_comm 2, Nat.mul_comm (p + 1) (p + 2)]
    simpa only [Nat.choose_one_right] using (Nat.add_one_mul_choose_eq (p + 1) 1).symm
  have hcount : 2 * D = ((p : ℝ) + 1) * ((p : ℝ) + 2) := by
    dsimp only [D]
    exact_mod_cast hcountNat
  have hleft : 3 + h = ((p : ℝ) + 1) * h := by linear_combination -hscale
  have hright : 3 + 2 * h = ((p : ℝ) + 2) * h := by linear_combination -hscale
  have hnorm : (3 + h) * (3 + 2 * h) = 2 * D * h ^ 2 := by
    calc
      _ = (((p : ℝ) + 1) * ((p : ℝ) + 2)) * h ^ 2 := by rw [hleft, hright]; ring
      _ = _ := by rw [← hcount]
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast (DimThree.word_counts_all p).2.1
  rw [hsum, hnorm]
  field_simp [hh.ne', hD.ne'] <;> ring


/-- The signed quadrature lower bound for the fourth-order joint moment. -/
def shortJointFourthQuadrature (h s d : ℝ) : ℝ :=
  let f (x : ℝ) := (x + h) * shortJointFourthPolynomial h d x * Real.exp (s * x)
  (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) *
    ((∫ x in (0 : ℝ)..3, f x) + h / 2 * (f 0 + f 3) +
      h ^ 2 / 12 * (deriv f 3 - deriv f 0) -
      h ^ 4 / 720 * (iteratedDeriv 3 f 3 - iteratedDeriv 3 f 0))

/-- A nonnegative signed quadrature remainder gives a lower bound on the original lattice. -/
theorem shortJointFourthQuadrature_le {p : ℕ} (hp : 11 ≤ p) {s d : ℝ}
    (hs : 0 ≤ s) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    shortJointFourthQuadrature (3 / (p : ℝ)) s d ≤ shortJointMomentFourth p s d := by
  let h : ℝ := 3 / (p : ℝ)
  let f (x : ℝ) := (x + h) * shortJointFourthPolynomial h d x * Real.exp (s * x)
  have hp₀ : 0 < p := (by decide : 0 < (11 : ℕ)).trans_le hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 ≤ h := div_nonneg (by norm_num) hpR.le
  have hh' : h ≤ 3 / 11 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hspan : (p : ℝ) * h = 3 := mul_div_cancel₀ 3 hpR.ne'
  have hdiff : ContDiff ℝ ⊤ f := shortJointFourthIntegrand_contDiff h d s
  have hd (j : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hdiff.differentiable_iteratedDeriv j (by simp) x).hasDerivAt
  have heq := D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.mesh_sum_eq
    (a := 0) (h := h) (n := p) (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) (hd 5)
    (hdiff.continuous_iteratedDeriv 6 le_top)
  have hrem := D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.meshRemainder_nonneg
    (a := 0) (n := p) hh (f6 := iteratedDeriv 6 f) fun x hx ↦
      shortJointFourthIntegrand_iteratedDeriv_nonneg 6 hh hh' hd₀ hd₁ hs hx.1
  have hsum := shortJointMomentFourth_eq_gridSum hp₀ s d
  change shortJointMomentFourth p s d =
    (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) *
      (h * ∑ n ∈ Finset.range (p + 1), f (h * n)) at hsum
  rw [hsum]
  unfold shortJointFourthQuadrature
  change (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) * _ ≤ _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [iteratedDeriv_zero, iteratedDeriv_one, zero_add, hspan] at heq
  have hnodes : (∑ i ∈ Finset.range (p + 1), f (h * (i : ℝ))) =
      ∑ i ∈ Finset.range (p + 1), f ((i : ℝ) * h) :=
    Finset.sum_congr rfl (fun i _ ↦ congrArg f (mul_comm h (i : ℝ)))
  rw [hnodes]
  exact (le_add_of_nonneg_right hrem).trans_eq heq.symm

/-- The scalar comparison at the signed quadrature lower bound suffices for the
mixed kernel sign throughout the short-gap strip. -/
theorem logKernel_mixed_neg_of_shortJointFourthQuadrature {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 1 / 2 ≤ u) (huv : u < v) (hd : v - u ≤ 1)
    (hcompare : 0 < compactRegularizedQ p u v - compactMixedT p u v
      (shortJointFourthQuadrature (3 / (p : ℝ)) ((u + v) / 2) (v - u))) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hu₀ : 0 < u := by linarith
  have hv : 1 / 2 ≤ v := hu.trans huv.le
  apply logKernel_mixed_neg_of_joint_lower hp₀ hu₀ huv
    (compactMixedT_strictAnti_of_slope hp₀ hu₀
      (reflectedHalfLogSlope_lt_two_add_spacing hp hv)).antitone
    ((shortJointFourthQuadrature_le hp (by linarith) (sub_nonneg.mpr huv.le) hd).trans
      (shortJointMomentFourth_le p u v))
  rwa [compactMixedQ_eq_regularized hp₀ hu₀ huv]

/-- Reflecting the joint density puts both closed quadratures on the same interval. -/
theorem shortJointFourthQuadrature_reflect {h : ℝ} (hh : 0 ≤ h) (s d : ℝ) :
    compactMarginalMeshDenominator h / 2 * shortJointFourthQuadrature h s d =
      compactClosedQuadrature h (fun x ↦ (2 + h - x) *
        shortJointFourthPolynomial h d (2 - x) * Real.exp (-s * x)) := by
  let f (r : ℝ) := (r + h) * shortJointFourthPolynomial h d r * Real.exp (s * r)
  let C := Real.exp (-2 * s)
  let g (x : ℝ) := (2 + h - x) * shortJointFourthPolynomial h d (2 - x) * Real.exp (-s * x)
  have hg : g = fun x ↦ C * f (2 - x) := by
    funext x
    have he : Real.exp (-s * x) = C * Real.exp (s * (2 - x)) := by
      unfold C
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [g, f]
    rw [he]
    ring
  have hint : (∫ x in (-1 : ℝ)..2, g x) = C * (∫ r in (0 : ℝ)..3, f r) := by
    rw [hg, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
    norm_num
  have hderiv (n : ℕ) (x : ℝ) : iteratedDeriv n g x =
      C * ((-1 : ℝ) ^ n * iteratedDeriv n f (2 - x)) := by
    rw [hg, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_sub]
    rfl
  have hleft : g (-1) = C * f 3 := by rw [hg]; norm_num
  have hright : g 2 = C * f 0 := by rw [hg]; norm_num
  have hden : compactMarginalMeshDenominator h ≠ 0 := by
    unfold compactMarginalMeshDenominator
    positivity
  change _ = compactClosedQuadrature h g
  unfold shortJointFourthQuadrature compactClosedQuadrature
  change compactMarginalMeshDenominator h / 2 *
      (2 * C / compactMarginalMeshDenominator h * ((∫ r in (0 : ℝ)..3, f r) +
        h / 2 * (f 0 + f 3) + h ^ 2 / 12 * (deriv f 3 - deriv f 0) -
        h ^ 4 / 720 * (iteratedDeriv 3 f 3 - iteratedDeriv 3 f 0))) = _
  rw [hint, hleft, hright, hderiv 1 2, hderiv 1 (-1), hderiv 3 2, hderiv 3 (-1)]
  norm_num [iteratedDeriv_one]
  field_simp [hden]
  ring

/-- The finite parameter-series coefficient for closed quadrature of a weighted
exponential density, before translation to the center of the parameter interval. -/
def compactClosedQuadratureSeriesCoeff (h : ℝ) (degree : ℕ) (weight : ℕ → ℝ) (n : ℕ) : ℝ :=
  weight n / (n.factorial : ℝ) * compactClosedQuadrature h (fun x ↦ x ^ (n + degree))

/-- A centered polynomial enclosure for a closed quadrature. Its two error bounds
control the infinite tail and the discarded terms of the translated polynomial. -/
theorem compactClosedQuadrature_shiftedSeries_sound
    {s t z h C center offset radius width : ℝ} {degree terms order : ℕ}
    {X : CompactTaylorModel.Model} (hb : CompactTaylorModel.InBox s t z)
    (hx : X.Encloses s t z offset) (hh : 0 ≤ h)
    (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |center| + |offset| ≤ radius) (hratio : 2 * radius < (terms : ℝ) - 2)
    (hw : |offset| ≤ width) {weight : ℕ → ℝ} (hweight : ∀ n, |weight n| ≤ C)
    (models : ℕ → CompactTaylorModel.Model)
    (hmodels : ∀ m < order, (models m).Encloses s t z
      (CompactTaylorModel.shiftedSeriesCoeff
        (compactClosedQuadratureSeriesCoeff h degree weight) terms center m))
    {shiftError tailError : ℚ}
    (hshift : width ^ order * ∑ n ∈ Finset.Ico order terms,
        |compactClosedQuadratureSeriesCoeff h degree weight n| *
          (n.choose order : ℝ) * radius ^ (n - order) ≤ (shiftError : ℝ))
    (htail : C * ((3 + h) * quadratureTailTerm degree 0 radius terms +
        h ^ 2 / 6 * quadratureTailTerm degree 1 radius terms +
        h ^ 4 / 360 * quadratureTailTerm degree 3 radius terms) /
        (1 - 2 * radius / ((terms : ℝ) - 2)) ≤ (tailError : ℝ)) :
    (((CompactTaylorModel.Model.series order models X).widen shiftError).widen tailError).Encloses
      s t z (compactClosedQuadrature h (fun x ↦ ∑' n : ℕ,
        (weight n * ((center + offset) ^ n / n.factorial)) * x ^ (n + degree))) := by
  have hseries := CompactTaylorModel.Model.shiftedSeries_sound hb hx horder hr hw
    (compactClosedQuadratureSeriesCoeff h degree weight) models hmodels hshift
  apply CompactTaylorModel.Model.widen_sound hseries
  have habs : |center + offset| ≤ radius := (abs_add_le _ _).trans hr
  have herror := compactClosedQuadrature_taylor_error_le
    (offset := degree) hh habs hterms hratio hweight
  have heq (n : ℕ) :
      weight n * ((center + offset) ^ n / (n.factorial : ℝ)) *
        compactClosedQuadrature h (fun x ↦ x ^ (n + degree)) =
      compactClosedQuadratureSeriesCoeff h degree weight n * (center + offset) ^ n := by
    simp only [compactClosedQuadratureSeriesCoeff, div_eq_mul_inv]
    ring
  simpa only [heq] using herror.trans htail

/-- The closed-mesh normalization and the negative score used by the exact short-gap
certificate. The marginal inputs are the regularized moment and its first two derivatives. -/
def shortQuadratureNegativeScore (p : ℕ) (u v : ℝ) : ℝ :=
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (t : ℝ) := (J * compactKappa p) * compactZ p t
  let slope (t : ℝ) := deriv q t / q t
  let a := 1 / u - slope (-u) / 2
  let c := 1 / v - slope (-v) / 2
  let δ := (slope v + slope (-v)) / 2
  let r := slope d
  let k := 1 / upperTailGap h u
  let γ := 1 + k + a
  let joint := J * shortJointFourthQuadrature h ((u + v) / 2) d
  let affine := -γ * ((2 + h - c) * joint +
    k * Real.exp (-(1 + h) * u) * (J + v ^ 2 * q v)) +
    k * Real.exp u * ((γ - c) * (J + d ^ 2 * q d) + d * (2 * q d + d * deriv q d)) -
    J * a * c
  let multiplier := a + δ + r + d * (iteratedDeriv 2 q d / q d / 2 - r ^ 2 / 4 +
    (a + δ) * r / 2 + a * δ)
  show ℝ from -(affine + v * Real.sqrt (q v * q d) * multiplier)

set_option maxRecDepth 2048 in
/-- The arithmetic score is the exact scaled gap between the radical and the affine term. -/
theorem shortQuadratureNegativeScore_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    shortQuadratureNegativeScore p u v = J * (compactRegularizedQ p u v -
      compactMixedT p u v (shortJointFourthQuadrature h ((u + v) / 2) (v - u))) := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let J : ℝ := (3 + h) * (3 + 2 * h) / 2
  let q (t : ℝ) := (J * compactKappa p) * compactZ p t
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 ≤ h := div_nonneg (by norm_num) hpR.le
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hκ : 0 < compactKappa p := by unfold compactKappa; positivity
  have hscale : 0 < J * compactKappa p := mul_pos hJ hκ
  have hderiv (t : ℝ) : deriv q t = (J * compactKappa p) *
      SmallCorner.integralMarginalDerivative p (compactKappa p) 1 t := by
    change deriv (fun x ↦ (J * compactKappa p) * compactZ p x) t = _
    rw [deriv_const_mul_field, ← iteratedDeriv_one, iteratedDeriv_compactZ_eq_integral hp]
  have hslope (t : ℝ) : deriv q t / q t = compactZSlope p t := by
    rw [hderiv, compactZSlope_eq hp t]
    dsimp only [q]
    rw [mul_div_mul_left _ _ hscale.ne']
  have hsecond (t : ℝ) : iteratedDeriv 2 q t / q t =
      SmallCorner.integralMarginalDerivative p (compactKappa p) 2 t / compactZ p t := by
    change iteratedDeriv 2 (fun x ↦ (J * compactKappa p) * compactZ p x) t / q t = _
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_compactZ_eq_integral hp]
    dsimp only [q]
    rw [mul_div_mul_left _ _ hscale.ne']
  have hderivD : deriv q d = q d * compactZSlope p d := by
    have hq : 0 < q d := mul_pos hscale (compactZ_pos hp d)
    exact (div_eq_iff hq.ne').mp (hslope d) |>.trans (mul_comm _ _)
  have hroot : Real.sqrt (q v * q d) =
      (J * compactKappa p) * Real.sqrt (compactZ p v * compactZ p d) := by
    rw [show q v * q d = (J * compactKappa p) ^ 2 * (compactZ p v * compactZ p d) by
      dsimp only [q]
      ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hscale.le]
  change shortQuadratureNegativeScore p u v = J * (compactRegularizedQ p u v -
    compactMixedT p u v (shortJointFourthQuadrature h ((u + v) / 2) d))
  dsimp only [q, J, h, d] at hslope hsecond hderivD hroot
  dsimp only [shortQuadratureNegativeScore, J, h, d]
  simp only [hslope, hsecond, hroot]
  rw [hderivD, compactMixedT_eq_cutoff hp hu hv]
  simp only [compactRegularizedQ, deriv_compactZSlope hp]
  ring

theorem logKernel_mixed_neg_of_shortQuadratureNegativeScore {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 1 / 2 ≤ u) (huv : u < v) (hd : v - u ≤ 1)
    (hscore : 0 < shortQuadratureNegativeScore p u v) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hu₀ : 0 < u := by linarith
  rw [shortQuadratureNegativeScore_eq hp₀ hu₀ (hu₀.trans huv)] at hscore
  apply logKernel_mixed_neg_of_shortJointFourthQuadrature hp hu huv hd
  have hh : 0 ≤ (3 : ℝ) / p := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity)).mp hscore

end

end RefinedBMV.PositiveCenter
