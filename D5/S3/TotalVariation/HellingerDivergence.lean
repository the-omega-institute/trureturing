/- GID: D5/S3/TotalVariation/HellingerDivergence
   generality: G
   mirror-B: D5/B/S3/TotalVariation/HellingerDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dominate squared Hellinger distance by KL and prove its basic metric laws. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `add_one_le_exp`, `one_sub_exp`, `Hellinger`,
     `Bhattacharyya`, `sum_sqrt_mul_sqrt_le`, `inner_mul_le_norm_mul_norm`,
     `Lp_add_le`, `Minkowski`, and `sqrt_eq_rpow`.
   * `Real.add_one_le_exp` gives the scalar estimate directly after substituting `-x`.
     No finite statistical Hellinger distance was found; the only Hellinger hits concern the
     unrelated Hellinger--Toeplitz theorem. `Real.Lp_add_le` specializes directly at exponent two,
     so the triangle inequality needs neither a new distance definition nor a normed-space wrapper.
   * Repository grep covered all 650 Lean declarations below `D5/S3`. In the relevant bucket it
     found the frozen KL, total-variation, Bhattacharyya, and squared-Hellinger declarations, but no
     KL domination or Hellinger metric-law theorem under another name.
-/

import D5.S3.TotalVariation.Hellinger

/-!
# Squared Hellinger distance and KL divergence

For nonnegative normalized finite mass functions with discrete absolute continuity, this module
proves `hellingerSq p q <= klDivergence p q`. It also records the unconditional nonnegativity and
symmetry of squared Hellinger distance, its exact zero set in square-root coordinates, separation
on the nonnegative cone, and the triangle inequality for `Real.sqrt (hellingerSq p q)`.

Separation is intentionally not stated for arbitrary real functions: `Real.sqrt` maps every
nonpositive real to zero. Thus the square-root Hellinger distance is only a pseudometric after
arbitrary real inputs are admitted, unlike total variation, which separates such functions
unconditionally.

Finally, `hellingerSq p q <= klDivergence p q` and
`hellingerSq p q / 2 <= totalVariation p q` cannot be chained into an upper bound on total
variation by KL divergence: both inequalities point away from squared Hellinger distance. Pinsker
and Bretagnolle--Huber provide the relevant upper controls on total variation.
-/

namespace D5.S3.TotalVariation.HellingerDivergence

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger

/-- Squared Hellinger distance is dominated by KL divergence for normalized nonnegative finite
mass functions under discrete absolute continuity `p << q`. -/
theorem hellinger_sq_le_kl_divergence {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    hellingerSq p q ≤ klDivergence p q := by
  have hkl : 0 ≤ klDivergence p q :=
    D5.S3.Divergence.GrandmotherTheorem.kl_divergence_nonneg p q hp hq hac
  have hbc : 0 ≤ bhattacharyya p q := by
    rw [bhattacharyya]
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg (p i * q i)
  have hexp := exp_neg_kl_divergence_le_bhattacharyya_sq p q hp hq.1 hac
  have hexp_half_sq :
      Real.exp (-klDivergence p q / 2) ^ 2 =
        Real.exp (-klDivergence p q) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hexp_half_le :
      Real.exp (-klDivergence p q / 2) ≤ bhattacharyya p q := by
    nlinarith [Real.exp_pos (-klDivergence p q / 2)]
  have hscalar :
      1 - Real.exp (-klDivergence p q / 2) ≤ klDivergence p q / 2 := by
    have hx : 0 ≤ klDivergence p q / 2 := div_nonneg hkl (by norm_num)
    have h := Real.add_one_le_exp (-klDivergence p q / 2)
    linarith
  calc
    hellingerSq p q = 2 * (1 - bhattacharyya p q) :=
      hellinger_sq_eq_two_sub p q hp hq
    _ ≤ 2 * (1 - Real.exp (-klDivergence p q / 2)) := by linarith
    _ ≤ klDivergence p q := by linarith

/-- The Hellinger--KL domination is strict for a point mass against `(1/4, 3/4)`. -/
theorem hellinger_sq_lt_kl_divergence_witness :
    hellingerSq
        (fun b : Bool => if b then (1 : ℝ) else 0)
        (fun b : Bool => if b then (1 / 4 : ℝ) else 3 / 4) <
      klDivergence
        (fun b : Bool => if b then (1 : ℝ) else 0)
        (fun b : Bool => if b then (1 / 4 : ℝ) else 3 / 4) := by
  let p := fun b : Bool => if b then (1 : ℝ) else 0
  let q := fun b : Bool => if b then (1 / 4 : ℝ) else 3 / 4
  have hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
    constructor
    · intro i
      cases i <;> simp [p]
    · simp [p]
  have hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 := by
    constructor
    · intro i
      cases i <;> norm_num [q]
    · norm_num [q, Fintype.sum_bool]
  have hsqrt_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have hhell : hellingerSq p q = 1 := by
    rw [hellinger_sq_eq_two_sub p q hp hq]
    norm_num [bhattacharyya, p, q, Fintype.sum_bool, hsqrt_quarter]
  have hkl : klDivergence p q = Real.log 4 := by
    norm_num [klDivergence, p, q, Fintype.sum_bool]
  change hellingerSq p q < klDivergence p q
  rw [hhell, hkl, Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
  exact Real.exp_one_lt_three.trans (by norm_num)

/-- Squared Hellinger distance is nonnegative for arbitrary finite real functions. -/
theorem hellinger_sq_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    0 ≤ hellingerSq p q := by
  rw [hellingerSq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Squared Hellinger distance is symmetric for arbitrary finite real functions. -/
theorem hellinger_sq_comm {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    hellingerSq p q = hellingerSq q p := by
  rw [hellingerSq, hellingerSq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For arbitrary finite real functions, squared Hellinger distance vanishes exactly when their
coordinatewise square roots agree. -/
theorem hellinger_sq_eq_zero_iff_sqrt_eq {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    hellingerSq p q = 0 ↔
      (fun i => Real.sqrt (p i)) = fun i => Real.sqrt (q i) := by
  constructor
  · intro h
    rw [hellingerSq] at h
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i)))).mp h
    funext i
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hterms i (Finset.mem_univ i)))
  · intro h
    rw [hellingerSq]
    apply Finset.sum_eq_zero
    intro i _
    rw [congrFun h i, sub_self]
    norm_num

/-- Arbitrary real inputs do not satisfy point separation: two distinct negative singleton
functions both have identically zero square roots. -/
theorem hellinger_sq_negative_counterexample :
    hellingerSq (fun _ : Unit => (-1 : ℝ)) (fun _ : Unit => (-2 : ℝ)) = 0 ∧
      (fun _ : Unit => (-1 : ℝ)) ≠ fun _ : Unit => (-2 : ℝ) := by
  constructor
  · simp [hellingerSq, Real.sqrt_eq_zero_of_nonpos]
  · intro h
    have hi := congrFun h ()
    norm_num at hi

/-- On the nonnegative cone, squared Hellinger distance separates finite real functions. Both
pointwise nonnegativity assumptions are needed to make `Real.sqrt` injective. -/
theorem hellinger_sq_eq_zero_iff {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    hellingerSq p q = 0 ↔ p = q := by
  rw [hellinger_sq_eq_zero_iff_sqrt_eq]
  constructor
  · intro h
    funext i
    exact (Real.sqrt_inj (hp i) (hq i)).mp (congrFun h i)
  · rintro rfl
    rfl

/-- The square root of squared Hellinger distance satisfies the triangle inequality for arbitrary
finite real functions. This is the exponent-two specialization of finite Minkowski. -/
theorem sqrt_hellinger_sq_triangle {ι : Type*} [Fintype ι] (p q r : ι → ℝ) :
    Real.sqrt (hellingerSq p r) ≤
      Real.sqrt (hellingerSq p q) + Real.sqrt (hellingerSq q r) := by
  rw [hellingerSq, hellingerSq, hellingerSq]
  rw [Real.sqrt_eq_rpow (∑ i, (Real.sqrt (p i) - Real.sqrt (r i)) ^ 2),
    Real.sqrt_eq_rpow (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2),
    Real.sqrt_eq_rpow (∑ i, (Real.sqrt (q i) - Real.sqrt (r i)) ^ 2)]
  have h := Real.Lp_add_le Finset.univ
    (fun i => Real.sqrt (p i) - Real.sqrt (q i))
    (fun i => Real.sqrt (q i) - Real.sqrt (r i))
    (p := (2 : ℝ)) (by norm_num)
  simpa only [Real.rpow_two, sq_abs, sub_add_sub_cancel] using h

end D5.S3.TotalVariation.HellingerDivergence
