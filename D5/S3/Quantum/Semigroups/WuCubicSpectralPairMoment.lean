import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import OmegaBuild.Commands

/-! The two-node Gaussian rule for the finite spectral law in Wu's cubic translation bound. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Set

namespace D5.S3.Quantum.Semigroups.WuCubicSpectralPairMoment

variable {ι : Type*} [Fintype ι]

/-- The variance of a spectral law of mean one. -/
def variance (mass z : ι → ℝ) : ℝ :=
  ∑ i, mass i * (z i - 1)^2

/-- The third moment about the mean one. -/
def thirdCenteredMoment (mass z : ι → ℝ) : ℝ :=
  ∑ i, mass i * (z i - 1)^3

/-- The two-node rule at `1-u` and `1+w` with masses `w/(u+w)` and `u/(u+w)`. -/
def pairAverage (u w : ℝ) (f : ℝ → ℝ) : ℝ :=
  w / (u + w) * f (1 - u) + u / (u + w) * f (1 + w)

/-- The Gaussian pair and its degree-three exactness on the finite spectral law. -/
structure IsGaussianPair (mass z : ι → ℝ) (lo hi u w : ℝ) : Prop where
  u_pos : 0 < u
  w_pos : 0 < w
  leftWeight_pos : 0 < w / (u + w)
  rightWeight_pos : 0 < u / (u + w)
  mul_eq_variance : u * w = variance mass z
  sub_eq_skew : w - u = thirdCenteredMoment mass z / variance mass z
  root_factor : ∀ y : ℝ, y ^ 2 -
    (thirdCenteredMoment mass z / variance mass z) * y - variance mass z = (y + u) * (y - w)
  left_mem : 1 - u ∈ Icc lo hi
  right_mem : 1 + w ∈ Icc lo hi
  left_support : ∃ i, 0 < mass i ∧ z i ≤ 1 - u
  right_support : ∃ i, 0 < mass i ∧ 1 + w ≤ z i
  moment_eq : ∀ n : ℕ, n ≤ 3 →
    (∑ i, mass i * z i ^ n) = pairAverage u w (fun x => x ^ n)

private theorem exists_le_of_centered (q y : ι → ℝ) {a : ℝ}
    (hq : ∀ i, 0 ≤ q i) (hqsum : 0 < ∑ i, q i)
    (hzero : ∑ i, q i * (y i - a) = 0) :
    ∃ i, 0 < q i ∧ y i ≤ a := by
  obtain ⟨j, -, hj⟩ := (Finset.sum_pos_iff_of_nonneg fun i _ => hq i).mp hqsum
  by_contra! h
  have hpos := Finset.sum_pos' (s := Finset.univ)
    (f := fun i => q i * (y i - a)) (fun i _ => by
      rcases (hq i).eq_or_lt with hz | hp
      · simp [← hz]
      · exact mul_nonneg hp.le (sub_nonneg.mpr (h i hp).le))
    ⟨j, Finset.mem_univ j, mul_pos hj (sub_pos.mpr (h j hj))⟩
  linarith

/-- The two roots of the centered quadratic give positive masses and lie in the
convex hull of the positive-mass support. Their raw moments agree in degrees zero through three. -/
theorem exists_gaussianPair (mass z : ι → ℝ) {lo hi : ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (htotal : ∑ i, mass i = 1)
    (hmean : ∑ i, mass i * z i = 1)
    (hsupport : ∀ i, 0 < mass i → z i ∈ Icc lo hi)
    (hvariance : 0 < variance mass z) :
    ∃ u w, IsGaussianPair mass z lo hi u w := by
  let v := variance mass z
  let c := thirdCenteredMoment mass z
  let k := c / v
  have hv : 0 < v := hvariance
  have hkc : k * v = c := div_mul_cancel₀ c hv.ne'
  let d := Real.sqrt (k ^ 2 + 4 * v)
  have hd : d ^ 2 = k ^ 2 + 4 * v := Real.sq_sqrt (by positivity)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hdlt : -d < k ∧ k < d := by
    constructor
    · by_contra! h
      nlinarith [mul_nonneg (show 0 ≤ -d - k by linarith)
        (show 0 ≤ d - k by linarith)]
    · by_contra! h
      nlinarith [mul_nonneg (show 0 ≤ k - d by linarith)
        (show 0 ≤ k + d by linarith)]
  let u := (d - k) / 2
  let w := (d + k) / 2
  have hu : 0 < u := by dsimp [u]; linarith [hdlt.2]
  have hw : 0 < w := by dsimp [w]; linarith [hdlt.1]
  have huw : u * w = v := by dsimp [u, w]; nlinarith only [hd]
  have hskew : w - u = k := by dsimp [u, w]; ring
  have hfactor (s : ℝ) : s ^ 2 - k * s - v = (s + u) * (s - w) := by
    rw [← hskew, ← huw]
    ring
  have hthird : u * w * (w - u) = c := by
    rw [huw, hskew, mul_comm, hkc]
  let y : ι → ℝ := fun i => z i - 1
  have hy : ∑ i, mass i * y i = 0 := by
    simp only [y, mul_sub, mul_one, Finset.sum_sub_distrib, hmean, htotal, sub_self]
  have hy₂ : ∑ i, mass i * y i ^ 2 = v := rfl
  have hy₃ : ∑ i, mass i * y i ^ 3 = c := rfl
  have orthogonal (t : ℝ) :
      ∑ i, mass i * ((y i + u) * (y i - w)) * (y i - t) = 0 := by
    calc
      _ = ∑ i, (mass i * y i ^ 3 - (k + t) * (mass i * y i ^ 2) +
          (k * t - v) * (mass i * y i) + (v * t) * mass i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hskew, ← huw]
        ring
      _ = 0 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hy₃, hy₂, hy, htotal, mul_zero, mul_one, add_zero]
        linear_combination -hkc
  have squaredMass (t : ℝ) : ∑ i, mass i * (y i - t) ^ 2 = v + t ^ 2 := by
    calc
      _ = ∑ i, (mass i * y i ^ 2 - (2 * t) * (mass i * y i) + t ^ 2 * mass i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hy₂, hy, htotal, mul_zero, sub_zero, mul_one]
  have leftZero : ∑ i, (mass i * (y i - w) ^ 2) * (y i - (-u)) = 0 := by
    rw [← orthogonal w]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have rightZero : ∑ i, (mass i * (y i - (-u)) ^ 2) * (-y i - (-w)) = 0 := by
    rw [← neg_zero, ← orthogonal (-u), ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have leftWitness : ∃ i, 0 < mass i ∧ z i ≤ 1 - u := by
    obtain ⟨i, hp, hi⟩ := exists_le_of_centered
      (fun i => mass i * (y i - w) ^ 2) y
      (fun i => mul_nonneg (hmass i) (sq_nonneg _))
      (by rw [squaredMass]; positivity) leftZero
    refine ⟨i, pos_of_mul_pos_left hp (sq_nonneg _), ?_⟩
    dsimp [y] at hi
    linarith
  have rightWitness : ∃ i, 0 < mass i ∧ 1 + w ≤ z i := by
    obtain ⟨i, hp, hi⟩ := exists_le_of_centered
      (fun i => mass i * (y i - (-u)) ^ 2) (fun i => -y i)
      (fun i => mul_nonneg (hmass i) (sq_nonneg _))
      (by rw [squaredMass]; positivity) rightZero
    refine ⟨i, pos_of_mul_pos_left hp (sq_nonneg _), ?_⟩
    dsimp [y] at hi
    linarith
  have hlo : lo ≤ 1 - u := by
    obtain ⟨i, hp, hi⟩ := leftWitness
    exact (hsupport i hp).1.trans hi
  have hhi : 1 + w ≤ hi := by
    obtain ⟨i, hp, hi'⟩ := rightWitness
    exact hi'.trans (hsupport i hp).2
  have horder : 1 - u < 1 + w := by linarith
  have hs : 0 < u + w := add_pos hu hw
  refine ⟨u, w, ⟨hu, hw, div_pos hw hs, div_pos hu hs, huw, hskew, hfactor,
    ⟨hlo, horder.le.trans hhi⟩, ⟨hlo.trans horder.le, hhi⟩, leftWitness, rightWitness, ?_⟩⟩
  have raw₂ : ∑ i, mass i * z i ^ 2 = 1 + v := by
    calc
      _ = ∑ i, (mass i + 2 * (mass i * y i) + mass i * y i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [y]
        ring
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, hy, hy₂]
  have raw₃ : ∑ i, mass i * z i ^ 3 = 1 + 3 * v + c := by
    calc
      _ = ∑ i, (mass i + 3 * (mass i * y i) + 3 * (mass i * y i ^ 2) +
          mass i * y i ^ 3) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [y]
        ring
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, hy, hy₂, hy₃]
  intro n hn
  interval_cases n
  · simp only [pow_zero, mul_one, htotal, pairAverage, ← add_div, add_comm w u, div_self hs.ne']
  · simp only [pow_one, hmean, pairAverage]
    field_simp [hs.ne']
    ring
  · rw [raw₂]
    simp only [pairAverage]
    field_simp [hs.ne']
    linear_combination -(u + w) * huw
  · rw [raw₃]
    simp only [pairAverage]
    field_simp [hs.ne']
    linear_combination -(u + w) * (3 * huw + hthird)

/-- The scalar entropy term in the centered cubic translation derivative. -/
def spectralEntropy (x : ℝ) : ℝ := x ^ 2 * Real.log x

private def entropySlope (x : ℝ) : ℝ := 2 * x * Real.log x + x

private theorem entropy_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt spectralEntropy (entropySlope x) x := by
  convert ((hasDerivAt_id' x).fun_pow 2).fun_mul (Real.hasDerivAt_log hx.ne') using 1
  · rfl
  · norm_num [entropySlope]
    field_simp [hx.ne']

private theorem entropySlope_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt entropySlope (2 * Real.log x + 3) x := by
  convert ((hasDerivAt_const_mul (x := x) 2).fun_mul (Real.hasDerivAt_log hx.ne')).fun_add
    (hasDerivAt_id' x) using 1
  · funext t
    unfold entropySlope
    ring
  · field_simp [hx.ne']; ring

private theorem entropy_second_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => 2 * Real.log t + 3) (2 / x) x := by
  simpa only [div_eq_mul_inv] using ((Real.hasDerivAt_log hx.ne').const_mul 2).add_const 3

private theorem entropy_third_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => 2 / t) (-2 / x ^ 2) x := by
  simpa only [div_eq_mul_inv, mul_neg, neg_mul] using (hasDerivAt_inv hx.ne').const_mul 2

private theorem rolle_positive {f f' : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (ha : 0 < a) (hab : a < b) (hfa : f a = 0) (hfb : f b = 0) :
    ∃ x ∈ Ioo a b, f' x = 0 :=
  exists_hasDerivAt_eq_zero hab
    (fun x hx => (h x (ha.trans_le hx.1)).continuousAt.continuousWithinAt)
    (hfa.trans hfb.symm) (fun x hx => h x (ha.trans hx.1))

private theorem exists_entropy_hermiteMajorant {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ A B : ℝ,
      let H := fun x => spectralEntropy a + entropySlope a * (x - a) +
        A * (x - a)^2 + B * (x - a)^3
      H a = spectralEntropy a ∧ H b = spectralEntropy b ∧
      HasDerivAt H (entropySlope a) a ∧ HasDerivAt H (entropySlope b) b ∧
      ∀ x, 0 < x → spectralEntropy x ≤ H x := by
  let d := b - a
  have hd : d ≠ 0 := (sub_pos.mpr hab).ne'
  let A := (3 * (spectralEntropy b - spectralEntropy a) -
    (2 * entropySlope a + entropySlope b) * d) / d ^ 2
  let B := (-2 * (spectralEntropy b - spectralEntropy a) +
    (entropySlope a + entropySlope b) * d) / d ^ 3
  let H := fun x => spectralEntropy a + entropySlope a * (x - a) +
    A * (x - a)^2 + B * (x - a)^3
  let H₁ := fun x => entropySlope a + 2 * A * (x - a) + 3 * B * (x - a)^2
  have hH (x : ℝ) : HasDerivAt H (H₁ x) x := by
    have hs := (hasDerivAt_id' x).sub_const a
    convert (((hs.const_mul (entropySlope a)).const_add (spectralEntropy a)).fun_add
      ((hs.fun_pow 2).const_mul A)).fun_add ((hs.fun_pow 3).const_mul B) using 1
    norm_num [H₁]; ring
  have hHa : H a = spectralEntropy a := by simp [H]
  have hHb : H b = spectralEntropy b := by
    change spectralEntropy a + entropySlope a * d + A * d ^ 2 + B * d ^ 3 = _
    dsimp only [A, B]
    field_simp [hd]; ring
  have hH₁a : H₁ a = entropySlope a := by simp [H₁]
  have hH₁b : H₁ b = entropySlope b := by
    change entropySlope a + 2 * A * d + 3 * B * d ^ 2 = _
    dsimp only [A, B]
    field_simp [hd]; ring
  have hHa' := hH a
  have hHb' := hH b
  rw [hH₁a] at hHa'
  rw [hH₁b] at hHb'
  refine ⟨A, B, hHa, hHb, hHa', hHb', ?_⟩
  intro x hx
  change spectralEntropy x ≤ H x
  rcases eq_or_ne x a with rfl | hxa
  · exact hHa.ge
  rcases eq_or_ne x b with rfl | hxb
  · exact hHb.ge
  by_contra! hbad
  let P := fun t => (t - a)^2 * (t - b)^2
  let P₁ := fun t => 2 * (t - a) * (t - b)^2 + 2 * (t - a)^2 * (t - b)
  let P₂ := fun t => 2 * (t - b)^2 + 8 * (t - a) * (t - b) + 2 * (t - a)^2
  let P₃ := fun t => 12 * (t - b) + 12 * (t - a)
  have hPx : 0 < P x := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxa))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hxb))
  -- Subtract the quartic that makes the error vanish at the third point.
  let k := (spectralEntropy x - H x) / P x
  have hk : 0 < k := div_pos (sub_pos.mpr hbad) hPx
  let g := fun t => spectralEntropy t - H t - k * P t
  let g₁ := fun t => entropySlope t - H₁ t - k * P₁ t
  let g₂ := fun t => 2 * Real.log t + 3 - (2 * A + 6 * B * (t - a)) - k * P₂ t
  let g₃ := fun t => 2 / t - 6 * B - k * P₃ t
  let g₄ := fun t => -2 / t ^ 2 - 24 * k
  have hg (t : ℝ) (ht : 0 < t) : HasDerivAt g (g₁ t) t := by
    have hs := (hasDerivAt_id' t).sub_const a
    have hr := (hasDerivAt_id' t).sub_const b
    have hP : HasDerivAt P (P₁ t) t := by
      convert (hs.fun_pow 2).fun_mul (hr.fun_pow 2) using 1
      norm_num [P₁]; ring
    exact ((entropy_hasDerivAt ht).sub (hH t)).sub (hP.const_mul k)
  have hg₁ (t : ℝ) (ht : 0 < t) : HasDerivAt g₁ (g₂ t) t := by
    have hs := (hasDerivAt_id' t).sub_const a
    have hr := (hasDerivAt_id' t).sub_const b
    have hP : HasDerivAt P₁ (P₂ t) t := by
      convert ((hs.const_mul 2).fun_mul (hr.fun_pow 2)).fun_add
        (((hs.fun_pow 2).const_mul 2).fun_mul hr) using 1
      norm_num [P₂]; ring
    have hH' : HasDerivAt H₁ (2 * A + 6 * B * (t - a)) t := by
      convert ((hs.const_mul (2 * A)).const_add (entropySlope a)).fun_add
        ((hs.fun_pow 2).const_mul (3 * B)) using 1
      norm_num; ring
    exact ((entropySlope_hasDerivAt ht).sub hH').sub (hP.const_mul k)
  have hg₂ (t : ℝ) (ht : 0 < t) : HasDerivAt g₂ (g₃ t) t := by
    have hs := (hasDerivAt_id' t).sub_const a
    have hr := (hasDerivAt_id' t).sub_const b
    have hP : HasDerivAt P₂ (P₃ t) t := by
      convert (((hr.fun_pow 2).const_mul 2).fun_add ((hs.const_mul 8).fun_mul hr)).fun_add
        ((hs.fun_pow 2).const_mul 2) using 1
      norm_num [P₃]; ring
    have hH' : HasDerivAt (fun t => 2 * A + 6 * B * (t - a)) (6 * B) t := by
      simpa using (hs.const_mul (6 * B)).const_add (2 * A)
    exact ((entropy_second_hasDerivAt ht).sub hH').sub (hP.const_mul k)
  have hg₃ (t : ℝ) (ht : 0 < t) : HasDerivAt g₃ (g₄ t) t := by
    have hs := (hasDerivAt_id' t).sub_const a
    have hr := (hasDerivAt_id' t).sub_const b
    have hP : HasDerivAt P₃ 24 t := by
      convert (hr.const_mul 12).fun_add (hs.const_mul 12) using 1
      norm_num
    convert ((entropy_third_hasDerivAt ht).sub_const (6 * B)).sub (hP.const_mul k) using 1
    dsimp [g₄]
    ring
  have hga : g a = 0 := by simp [g, hHa, P]
  have hgb : g b = 0 := by simp [g, hHb, P]
  have hgx : g x = 0 := by simp [g, k, div_mul_cancel₀ _ hPx.ne']
  have hg₁a : g₁ a = 0 := by simp [g₁, hH₁a, P₁]
  have hg₁b : g₁ b = 0 := by simp [g₁, hH₁b, P₁]
  -- Rolle in the two gaps and the derivative conditions give four distinct zeros.
  obtain ⟨r, s, t, q, hr, hrs, hst, htq, er, es, et, eq⟩ :
      ∃ r s t q : ℝ, 0 < r ∧ r < s ∧ s < t ∧ t < q ∧
        g₁ r = 0 ∧ g₁ s = 0 ∧ g₁ t = 0 ∧ g₁ q = 0 := by
    by_cases hxa' : x < a
    · obtain ⟨r, hr, er⟩ := rolle_positive hg hx hxa' hgx hga
      obtain ⟨t, ht, et⟩ := rolle_positive hg ha hab hga hgb
      exact ⟨r, a, t, b, hx.trans hr.1, hr.2, ht.1, ht.2, er, hg₁a, et, hg₁b⟩
    by_cases hxb' : x < b
    · have hax : a < x := lt_of_le_of_ne (le_of_not_gt hxa') hxa.symm
      obtain ⟨s, hs, es⟩ := rolle_positive hg ha hax hga hgx
      obtain ⟨t, ht, et⟩ := rolle_positive hg hx hxb' hgx hgb
      exact ⟨a, s, t, b, ha, hs.1, hs.2.trans ht.1, ht.2, hg₁a, es, et, hg₁b⟩
    · have hbx : b < x := lt_of_le_of_ne (le_of_not_gt hxb') hxb.symm
      obtain ⟨s, hs, es⟩ := rolle_positive hg ha hab hga hgb
      obtain ⟨q, hq, eq⟩ := rolle_positive hg (ha.trans hab) hbx hgb hgx
      exact ⟨a, s, b, q, ha, hs.1, hs.2, hq.1, hg₁a, es, hg₁b, eq⟩
  obtain ⟨r₂, hr₂, er₂⟩ := rolle_positive hg₁ hr hrs er es
  obtain ⟨s₂, hs₂, es₂⟩ := rolle_positive hg₁ (hr.trans hrs) hst es et
  obtain ⟨t₂, ht₂, et₂⟩ := rolle_positive hg₁ (hr.trans (hrs.trans hst)) htq et eq
  obtain ⟨r₃, hr₃, er₃⟩ := rolle_positive hg₂ (hr.trans hr₂.1) (hr₂.2.trans hs₂.1) er₂ es₂
  obtain ⟨s₃, hs₃, es₃⟩ := rolle_positive hg₂ (hr.trans (hrs.trans hs₂.1))
    (hs₂.2.trans ht₂.1) es₂ et₂
  obtain ⟨ξ, hξ, eξ⟩ := rolle_positive hg₃ (hr.trans (hr₂.1.trans hr₃.1))
    (hr₃.2.trans hs₃.1) er₃ es₃
  have hξpos : 0 < ξ := hr.trans (hr₂.1.trans (hr₃.1.trans hξ.1))
  have hnegative : g₄ ξ < 0 := by
    exact sub_neg_of_lt (lt_trans (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hξpos))
      (mul_pos (by norm_num) hk))
  exact hnegative.ne eξ

private theorem cubic_exact {mass z : ι → ℝ} {lo hi u w : ℝ}
    (hp : IsGaussianPair mass z lo hi u w) (C₀ C₁ C₂ C₃ : ℝ) :
    (∑ i, mass i * (C₀ + C₁ * z i + C₂ * z i ^ 2 + C₃ * z i ^ 3)) =
      pairAverage u w (fun x => C₀ + C₁ * x + C₂ * x ^ 2 + C₃ * x ^ 3) := by
  have h₀ := hp.moment_eq 0 (by decide)
  have h₁ := hp.moment_eq 1 (by decide)
  have h₂ := hp.moment_eq 2 (by decide)
  have h₃ := hp.moment_eq 3 (by decide)
  simp only [pow_zero, pow_one, mul_one] at h₀ h₁
  calc
    _ = ∑ i, (C₀ * mass i + C₁ * (mass i * z i) + C₂ * (mass i * z i ^ 2) +
        C₃ * (mass i * z i ^ 3)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h₀, h₁, h₂, h₃, pairAverage]
      ring

/-- The Gaussian pair provides an upper envelope for the actual spectral entropy,
by the cubic that interpolates its values and first derivatives at the nodes. -/
theorem IsGaussianPair.entropy_le {mass z : ι → ℝ} {lo hi u w : ℝ}
    (hp : IsGaussianPair mass z lo hi u w) (hlo : 0 < lo)
    (hmass : ∀ i, 0 ≤ mass i) (hsupport : ∀ i, 0 < mass i → z i ∈ Icc lo hi) :
    (∑ i, mass i * spectralEntropy (z i)) ≤ pairAverage u w spectralEntropy := by
  let a := 1 - u
  let b := 1 + w
  have ha : 0 < a := hlo.trans_le hp.left_mem.1
  have hab : a < b := by dsimp [a, b]; linarith [hp.u_pos, hp.w_pos]
  obtain ⟨A, B, hHa, hHb, -, -, hmajorant⟩ := exists_entropy_hermiteMajorant ha hab
  let H := fun x => spectralEntropy a + entropySlope a * (x - a) +
    A * (x - a)^2 + B * (x - a)^3
  have hexact : (∑ i, mass i * H (z i)) = pairAverage u w H := by
    have hH : H = fun x =>
        (spectralEntropy a - entropySlope a * a + A * a ^ 2 - B * a ^ 3) +
        (entropySlope a - 2 * A * a + 3 * B * a ^ 2) * x +
        (A - 3 * B * a) * x ^ 2 + B * x ^ 3 := by
      funext x
      dsimp only [H]
      ring
    rw [hH]
    exact cubic_exact hp _ _ _ _
  calc
    _ ≤ ∑ i, mass i * H (z i) := by
      apply Finset.sum_le_sum
      intro i _
      rcases (hmass i).eq_or_lt with hz | hp'
      · simp [← hz]
      · exact mul_le_mul_of_nonneg_left (hmajorant (z i) (hlo.trans_le (hsupport i hp').1)) hp'.le
    _ = pairAverage u w H := hexact
    _ = pairAverage u w spectralEntropy := by
      change w / (u + w) * H a + u / (u + w) * H b = _
      rw [show H a = spectralEntropy a from hHa, show H b = spectralEntropy b from hHb]
      rfl

/-- The Gaussian rule bounds the joint entropy and cubic-mass expression in Wu's
cubic translation derivative by its value on a positive two-node law. -/
theorem exists_gaussianPair_entropyEnvelope (mass z : ι → ℝ) {lo hi : ℝ}
    (hlo : 0 < lo) (hmass : ∀ i, 0 ≤ mass i) (htotal : ∑ i, mass i = 1)
    (hmean : ∑ i, mass i * z i = 1)
    (hsupport : ∀ i, 0 < mass i → z i ∈ Icc lo hi)
    (hvariance : 0 < variance mass z) :
    ∃ u w, IsGaussianPair mass z lo hi u w ∧
      3 * (∑ i, mass i * spectralEntropy (z i)) -
          (∑ i, mass i * z i ^ 2) * Real.log (∑ i, mass i * z i ^ 3) ≤
        3 * pairAverage u w spectralEntropy -
          pairAverage u w (fun x => x ^ 2) * Real.log (pairAverage u w (fun x => x ^ 3)) := by
  obtain ⟨u, w, hp⟩ := exists_gaussianPair mass z hmass htotal hmean hsupport hvariance
  refine ⟨u, w, hp, ?_⟩
  rw [hp.moment_eq 2 (by decide), hp.moment_eq 3 (by decide)]
  linarith only [hp.entropy_le hlo hmass hsupport]

end D5.S3.Quantum.Semigroups.WuCubicSpectralPairMoment
