/- GID: D5/S1/Recurrence/OEISA400645BoundedError
   generality: I
   mirror-B: D5/B/S1/Recurrence/OEISA400645BoundedError
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Every A400645 source sequence satisfies a_n = c λ^n + O(1) with c > 0, and a_(n+1)/a_n = λ + O(λ^(-n)). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#350)
escape_witness: other_roots (the complex roots of y^4 - y^3 - y^2 - y + 1 other than r have
  modulus below √r: the polynomial factors as (y^2 - β y + 1)(y^2 - (1 - β) y + 1), the first
  factor has the real roots r and β - r, the second has roots on the unit circle),
  rootMultiplicity_charPoly (r is a simple root, the derivative being positive at r) and the
  rationalization in result (a_(j+23)^2 = L r^j + O(r^(j/2)) gives a_n = c λ^n + O(1), and the
  ratio rate follows by dividing the bounded errors by a_n >= c λ^n / 2).
proof_shape:
  charPoly: definition; consumers: every lemma below.
  charPoly_natDegree: bind-only helper; consumer: charPoly_sum.
  charPoly_sum: bind-only helper; consumer: forcing_bound.
  charPoly_eval: bind-only helper; consumer: rootMultiplicity_charPoly.
  forcing_bound: bind-only helper (source_error at j + 26 after unfolding radicand and b);
    consumer: result.
  rootMultiplicity_charPoly, other_roots: content; consumer: result.
  result: content.
Direct frozen dependencies (module statement_id):
  D5/S1/Recurrence/Asymptotic/DominantRootForcing (result),
    sha256:1d9580e02dfd6fc17ce8d9039a9444783c195aa2b491d01ec9b830fd96091820;
  D5/S1/Recurrence/OEISA400645 (IsSourceSequence, radicand, squaredLimit, limitingRatio, b,
    source_error, square_asymptotic, r_bounds, r_quad, r_poly; the last six made public here for
    reuse), sha256:6b9935aa3f2f34c16302ab77311ac7fb8824542a3447a5f9a6013494c199e7aa;
  D5/S0/Tower/NonPisotFrontier/BetaThirteen (betaThirteen, betaThirteen_quadratic,
    two_lt_betaThirteen, sqrt_thirteen_bounds),
    sha256:cc19b57aaf3e1c818ccd8e593f82bbb5cfe0d926845fc6592e52fd2240bd66ab.
Search record (§3.1): D5/S1/Recurrence/OEISA400645 proves the ratio limit and the positive square
  asymptotic b a n / r^n -> L but no rate; OEISA400645FixedLagGrowth proves fixed-lag and
  logarithmic limits only; no D5 declaration states a bounded absolute error for A400645.
-/

import D5.S1.Recurrence.OEISA400645
import D5.S1.Recurrence.Asymptotic.DominantRootForcing

set_option autoImplicit false

noncomputable section

/-! # Bounded absolute error and ratio rate for A400645

For every source sequence of the frozen module `D5/S1/Recurrence/OEISA400645` there is `c > 0` with
`a n = c λ^n + O(1)` and `a (n + 1) / a n = λ + O(λ^(-n))`, where `λ = √r` is the limiting ratio.
The squares `a (j + 23)^2` satisfy the recurrence with characteristic polynomial
`y^4 - y^3 - y^2 - y + 1` up to the rounding error `O(λ^j)`; dominant-root forcing at `q = √r`
gives `a (j + 23)^2 = L r^j + O(r^(j/2))`, and rationalizing the square-root difference gives the
bounded error.
-/

namespace D5.S1.Recurrence.OEISA400645BoundedError

open Polynomial Asymptotics Filter
open D5.S1.Recurrence.OEISA400645
open D5.S0.Tower.NonPisotFrontier.BetaThirteen

/-- The characteristic polynomial `y^4 - y^3 - y^2 - y + 1` of the squared recurrence. -/
def charPoly : ℝ[X] := X ^ 4 - X ^ 3 - X ^ 2 - X + 1

private theorem charPoly_natDegree : charPoly.natDegree = 4 := by
  unfold charPoly
  compute_degree!

theorem charPoly_sum (u : ℕ → ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (charPoly.natDegree + 1), charPoly.coeff k * u (j + k) =
      u j - u (j + 1) - u (j + 2) - u (j + 3) + u (j + 4) := by
  rw [charPoly_natDegree]
  simp [Finset.sum_range_succ, charPoly, coeff_X_pow, coeff_X, coeff_one]
  ring

private theorem charPoly_eval (y : ℝ) : charPoly.eval y = y ^ 4 - y ^ 3 - y ^ 2 - y + 1 := by
  simp [charPoly]

theorem rootMultiplicity_charPoly : charPoly.rootMultiplicity squaredLimit = 1 := by
  have hr := r_bounds
  have hP0 : charPoly ≠ 0 := fun h => by
    have := charPoly_eval 0
    rw [h, eval_zero] at this
    norm_num at this
  have hroot : charPoly.IsRoot squaredLimit := by
    rw [IsRoot, charPoly_eval]
    exact r_poly
  have hpos : 0 < charPoly.rootMultiplicity squaredLimit :=
    (rootMultiplicity_pos hP0).mpr hroot
  have hnot : ¬ 1 < charPoly.rootMultiplicity squaredLimit := by
    rw [one_lt_rootMultiplicity_iff_isRoot hP0]
    rintro ⟨-, hd⟩
    rw [IsRoot] at hd
    simp [charPoly] at hd
    nlinarith [hr.1]
  omega

/-- Every complex root of `charPoly` other than `squaredLimit` has modulus below its square
root: the polynomial is `(y² - β y + 1)(y² - (1 - β) y + 1)` with `β = (1 + √13)/2`. -/
theorem other_roots (z : ℂ) (hz : (charPoly.map (algebraMap ℝ ℂ)).IsRoot z)
    (hne : z ≠ (squaredLimit : ℂ)) : ‖z‖ < Real.sqrt squaredLimit := by
  have hr := r_bounds
  have hq := r_quad
  have hβ := betaThirteen_quadratic
  have hβ2 := two_lt_betaThirteen
  have hβ3 : betaThirteen < 5 / 2 := by
    have := sqrt_thirteen_bounds.2
    simp only [betaThirteen]
    linarith
  have hz' : z ^ 4 - z ^ 3 - z ^ 2 - z + 1 = 0 := by
    simpa [IsRoot, charPoly] using hz
  have hfac : (z ^ 2 - (betaThirteen : ℂ) * z + 1) * (z ^ 2 - (1 - (betaThirteen : ℂ)) * z + 1)
      = 0 := by
    have hβC : (betaThirteen : ℂ) ^ 2 = betaThirteen + 3 := by exact_mod_cast hβ
    linear_combination hz' - z ^ 2 * hβC
  have hsq : Complex.normSq z < squaredLimit := by
    rcases mul_eq_zero.mp hfac with h1 | h2
    · -- the real pair `squaredLimit`, `β - squaredLimit`
      have hqC : (squaredLimit : ℂ) ^ 2 - (betaThirteen : ℂ) * squaredLimit + 1 = 0 := by
        exact_mod_cast hq
      have hprod : (z - squaredLimit) * (z - (betaThirteen - squaredLimit)) = 0 := by
        linear_combination h1 - hqC
      have hz2 : z = ((betaThirteen - squaredLimit : ℝ) : ℂ) := by
        have := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
        rw [sub_eq_zero] at this
        rw [this]
        push_cast
        ring
      rw [hz2, Complex.normSq_ofReal]
      nlinarith
    · -- the unit-circle pair
      set t : ℝ := 1 - betaThirteen with ht
      have htC : (1 - (betaThirteen : ℂ)) = (t : ℂ) := by rw [ht]; push_cast; ring
      rw [htC] at h2
      have hre := congrArg Complex.re h2
      have him := congrArg Complex.im h2
      simp [sq, Complex.mul_re, Complex.mul_im] at hre him
      have hy : z.im ≠ 0 := by
        intro h0
        rw [h0] at hre
        nlinarith [sq_nonneg (z.re - t / 2)]
      have hx : z.re = t / 2 := by
        have : z.im * (2 * z.re - t) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left hy
        linarith
      rw [Complex.normSq_apply]
      rw [hx] at hre
      nlinarith
  rw [Complex.norm_def]
  exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg z) hsq

/-- The squares `b a j = a (j + 23)^2` satisfy the characteristic recurrence up to an error of
size at most `2 a (j + 26)`. -/
private theorem forcing_bound {a : ℕ → ℕ} (ha : IsSourceSequence a) (j : ℕ) :
    |∑ k ∈ Finset.range (charPoly.natDegree + 1), charPoly.coeff k * b a (j + k)| ≤
      2 * (a (j + 26) : ℝ) := by
  rw [charPoly_sum]
  have he := source_error ha (j + 26) (by omega)
  have hrad : (radicand a (j + 26) : ℝ) = (a (j + 26) : ℝ) ^ 2 + (a (j + 25) : ℝ) ^ 2 +
      (a (j + 24) : ℝ) ^ 2 - (a (j + 23) : ℝ) ^ 2 := by
    simp only [radicand, show j + 26 - 1 = j + 25 by omega, show j + 26 - 2 = j + 24 by omega,
      show j + 26 - 3 = j + 23 by omega]
    push_cast
    ring
  rw [hrad] at he
  simp only [b, show j + 1 + 23 = j + 24 by omega, show j + 2 + 23 = j + 25 by omega,
    show j + 3 + 23 = j + 26 by omega, show j + 4 + 23 = j + 26 + 1 by omega]
  convert he using 2
  ring

/-- Bounded absolute error and ratio rate for A400645: every source sequence satisfies
`a n = c λ^n + O(1)` for some `c > 0`, and `a (n + 1) / a n = λ + O(λ^(-n))`, where
`λ = limitingRatio`. -/
theorem result :
    ∀ a : ℕ → ℕ, IsSourceSequence a → ∃ c : ℝ, 0 < c ∧
      (fun n => (a n : ℝ) - c * limitingRatio ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (a (n + 1) : ℝ) / a n - limitingRatio) =O[atTop]
        (fun n => (limitingRatio ^ n)⁻¹) := by
  intro a ha
  obtain ⟨L, hL, hlim⟩ := square_asymptotic ha
  have hr := r_bounds
  have hr0 : 0 < squaredLimit := by linarith
  have hLamDef : limitingRatio = Real.sqrt squaredLimit := rfl
  have hs0 : 0 < Real.sqrt squaredLimit := Real.sqrt_pos.mpr hr0
  have hs1 : 1 < Real.sqrt squaredLimit := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
  have hsq : Real.sqrt squaredLimit ^ 2 = squaredLimit := Real.sq_sqrt hr0.le
  have hspow : ∀ j : ℕ, (Real.sqrt squaredLimit ^ j) ^ 2 = squaredLimit ^ j := fun j => by
    rw [← pow_mul, mul_comm, pow_mul, hsq]
  have hsR : Real.sqrt squaredLimit < |squaredLimit| := by
    rw [abs_of_pos hr0]
    nlinarith
  -- the coefficient `L` is the leading coefficient of the squares
  have hlo : (fun j => b a j - L * squaredLimit ^ j) =o[atTop] (fun j => squaredLimit ^ j) := by
    rw [isLittleO_iff_tendsto (fun j h => absurd h (pow_ne_zero _ hr0.ne'))]
    have h := hlim.sub_const L
    rw [sub_self] at h
    refine h.congr fun j => ?_
    have : squaredLimit ^ j ≠ 0 := pow_ne_zero _ hr0.ne'
    field_simp
  -- the forcing is `O(√r^j)`
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show L < L + 1 by linarith)))
  set K := Real.sqrt ((L + 1) * squaredLimit ^ 3) with hKdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = (L + 1) * squaredLimit ^ 3 := Real.sq_sqrt (by positivity)
  have he : (fun j => ∑ k ∈ Finset.range (charPoly.natDegree + 1),
      charPoly.coeff k * b a (j + k)) =O[atTop] (fun j => Real.sqrt squaredLimit ^ j) := by
    refine IsBigO.of_bound (2 * K) (eventually_atTop.mpr ⟨N, fun j hj => ?_⟩)
    have h1 := forcing_bound ha j
    have h2 := hN (j + 3) (by omega)
    rw [div_lt_iff₀ (pow_pos hr0 _)] at h2
    have hb3 : b a (j + 3) = (a (j + 26) : ℝ) ^ 2 := by
      simp only [b, show j + 3 + 23 = j + 26 by omega]
    have hK : (a (j + 26) : ℝ) ≤ K * Real.sqrt squaredLimit ^ j := by
      refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).mp ?_
      rw [mul_pow, hKsq, hspow, ← hb3]
      calc b a (j + 3) ≤ (L + 1) * squaredLimit ^ (j + 3) := h2.le
        _ = (L + 1) * squaredLimit ^ 3 * squaredLimit ^ j := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs0 j)]
    linarith
  have hmain := (D5.S1.Recurrence.Asymptotic.DominantRootForcing.result).2 charPoly squaredLimit
    (Real.sqrt squaredLimit) rootMultiplicity_charPoly hs0 hsR other_roots (b a) _ L
    (fun j => rfl) hlo he
  -- rationalize: `a (j + 23) = √L √r^j + O(1)`
  obtain ⟨C, hC⟩ := hmain.bound
  obtain ⟨M, hM⟩ := eventually_atTop.mp hC
  have hc0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hshift : ∀ j, M ≤ j →
      |(a (j + 23) : ℝ) - Real.sqrt L * Real.sqrt squaredLimit ^ j| ≤ |C| / Real.sqrt L := by
    intro j hj
    have hb := hM j hj
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs0 j)] at hb
    set x : ℝ := (a (j + 23) : ℝ)
    set y : ℝ := Real.sqrt L * Real.sqrt squaredLimit ^ j
    have hx : 0 ≤ x := Nat.cast_nonneg _
    have hy : 0 < y := by positivity
    have hdiff : b a j - L * squaredLimit ^ j = (x - y) * (x + y) := by
      have : y ^ 2 = L * squaredLimit ^ j := by rw [mul_pow, Real.sq_sqrt hL.le, hspow]
      simp only [b, x]
      nlinarith [this]
    rw [hdiff, abs_mul, abs_of_pos (by linarith : 0 < x + y)] at hb
    rw [le_div_iff₀ hc0]
    have hpos : 0 < Real.sqrt squaredLimit ^ j := pow_pos hs0 j
    have h3 : |x - y| * y ≤ |C| * Real.sqrt squaredLimit ^ j := by
      have := abs_nonneg (x - y)
      nlinarith [le_abs_self C]
    have h4 : |x - y| * Real.sqrt L * Real.sqrt squaredLimit ^ j ≤
        |C| * Real.sqrt squaredLimit ^ j := by
      simpa [y, mul_assoc] using h3
    nlinarith
  set c := Real.sqrt L / Real.sqrt squaredLimit ^ 23 with hcdef
  have hc : 0 < c := by positivity
  set B := |C| / Real.sqrt L with hBdef
  have hdev : ∀ n, M + 23 ≤ n → |(a n : ℝ) - c * limitingRatio ^ n| ≤ B := by
    intro n hn
    have h := hshift (n - 23) (by omega)
    rw [show n - 23 + 23 = n by omega] at h
    convert h using 3
    rw [hLamDef, hcdef, show n = (n - 23) + 23 by omega, pow_add]
    field_simp
    rw [show n - 23 + 23 - 23 = n - 23 by omega]
  refine ⟨c, hc, IsBigO.of_bound B (eventually_atTop.mpr ⟨M + 23, fun n hn => ?_⟩), ?_⟩
  · rw [Real.norm_eq_abs, norm_one, mul_one]
    exact hdev n hn
  -- the ratio rate
  have hB0 : 0 ≤ B := by positivity
  have hgrow : Tendsto (fun n : ℕ => limitingRatio ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by rw [hLamDef]; exact hs1)
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hgrow.eventually_ge_atTop (2 * B / c))
  refine IsBigO.of_bound (2 * B * (1 + limitingRatio) / c)
    (eventually_atTop.mpr ⟨max (M + 23) P, fun n hn => ?_⟩)
  have hn1 : M + 23 ≤ n := le_of_max_le_left hn
  have hn2 : P ≤ n := le_of_max_le_right hn
  have hLam0 : 0 < limitingRatio := by rw [hLamDef]; exact hs0
  have hpow : 0 < limitingRatio ^ n := pow_pos hLam0 n
  have hd0 := hdev n hn1
  have hd1 := hdev (n + 1) (by omega)
  have hbig : 2 * B / c ≤ limitingRatio ^ n := hP n hn2
  have hbig' : 2 * B ≤ c * limitingRatio ^ n := by
    rw [div_le_iff₀ hc] at hbig
    linarith
  have hlow : c * limitingRatio ^ n / 2 ≤ (a n : ℝ) := by
    have := (abs_le.mp hd0).1
    linarith
  have hapos : 0 < (a n : ℝ) := by
    have : 0 < c * limitingRatio ^ n := by positivity
    linarith
  have hnum : |(a (n + 1) : ℝ) - limitingRatio * a n| ≤ B * (1 + limitingRatio) := by
    have hsplit : (a (n + 1) : ℝ) - limitingRatio * a n =
        ((a (n + 1) : ℝ) - c * limitingRatio ^ (n + 1)) -
          limitingRatio * ((a n : ℝ) - c * limitingRatio ^ n) := by ring
    rw [hsplit]
    calc _ ≤ |(a (n + 1) : ℝ) - c * limitingRatio ^ (n + 1)| +
          |limitingRatio * ((a n : ℝ) - c * limitingRatio ^ n)| := abs_sub _ _
      _ = |(a (n + 1) : ℝ) - c * limitingRatio ^ (n + 1)| +
          limitingRatio * |(a n : ℝ) - c * limitingRatio ^ n| := by
          rw [abs_mul, abs_of_pos hLam0]
      _ ≤ B + limitingRatio * B := by gcongr
      _ = B * (1 + limitingRatio) := by ring
  have hratio : (a (n + 1) : ℝ) / a n - limitingRatio =
      ((a (n + 1) : ℝ) - limitingRatio * a n) / a n := by
    field_simp
  rw [hratio, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hapos,
    abs_of_pos (inv_pos.mpr hpow), div_le_iff₀ hapos]
  calc |(a (n + 1) : ℝ) - limitingRatio * a n| ≤ B * (1 + limitingRatio) := hnum
    _ = 2 * B * (1 + limitingRatio) / c * (limitingRatio ^ n)⁻¹ *
        (c * limitingRatio ^ n / 2) := by
        field_simp
    _ ≤ 2 * B * (1 + limitingRatio) / c * (limitingRatio ^ n)⁻¹ * (a n : ℝ) := by
        gcongr

end D5.S1.Recurrence.OEISA400645BoundedError
