/- GID: D5/S3/TotalVariation/Hellinger
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Hellinger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define squared Hellinger distance and compare it with total variation. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `Hellinger`, `Bhattacharyya`,
     `sqrt.*sub.*sqrt`, `sqrt.*-.*sqrt`, `sqrt_sq_eq_abs`, and `abs_le_sqrt`.
   * The only Hellinger hits concern the unrelated Hellinger--Toeplitz theorem. No finite-real
     statistical Hellinger distance or direct `(sqrt a - sqrt b)^2 <= |a - b|` lemma was found.
     The primitive square-root and absolute-value lemmas are reused below.
   * Repository grep over every Lean declaration below `D5/S3` found the frozen finite-real
     total variation and Bhattacharyya coefficient, but no Hellinger distance or lower bracket.

   The lower bracket proved here is the new comparison: it is obtained pointwise and needs neither
   nonnegativity nor normalization. The final upper-bracket theorem is deliberately only a thin
   restatement of the frozen Bhattacharyya square bound in Hellinger coordinates.
-/

import D5.S3.TotalVariation.Bhattacharyya

namespace D5.S3.TotalVariation.Hellinger

open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Pinsker

/-- The squared Hellinger distance of two finite real mass functions. This intrinsic definition
records the coordinatewise square-root geometry independently of Bhattacharyya affinity. -/
noncomputable def hellingerSq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2

/-- Every finite real function has zero squared Hellinger distance from itself. -/
theorem hellinger_sq_self {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    hellingerSq p p = 0 := by
  simp [hellingerSq]

/-- Algebraic expansion of squared Hellinger distance, valid for arbitrary real inputs. This
pins the behavior outside the nonnegative mass-function domain as well as inside it. -/
theorem hellinger_sq_eq_sum_expanded {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    hellingerSq p q =
      ∑ i : ι, (Real.sqrt (p i) ^ 2 + Real.sqrt (q i) ^ 2 -
        2 * (Real.sqrt (p i) * Real.sqrt (q i))) := by
  rw [hellingerSq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For nonnegative finite mass functions, squared Hellinger distance is the sum of their
total masses minus twice their Bhattacharyya affinity. No normalization is needed. -/
theorem hellinger_sq_eq_sum_add_sub_two_bhattacharyya
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    hellingerSq p q =
      (∑ i, p i) + (∑ i, q i) - 2 * bhattacharyya p q := by
  rw [hellinger_sq_eq_sum_expanded, bhattacharyya]
  calc
    (∑ i : ι, (Real.sqrt (p i) ^ 2 + Real.sqrt (q i) ^ 2 -
        2 * (Real.sqrt (p i) * Real.sqrt (q i)))) =
        ∑ i, (p i + q i - 2 * Real.sqrt (p i * q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i),
        Real.sqrt_mul (hp i) (q i)]
    _ = (∑ i, p i) + (∑ i, q i) -
        2 * ∑ i, Real.sqrt (p i * q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- On nonnegative normalized mass functions, squared Hellinger distance is twice one minus
Bhattacharyya affinity. This is a theorem connecting two independently defined quantities. -/
theorem hellinger_sq_eq_two_sub {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    hellingerSq p q = 2 * (1 - bhattacharyya p q) := by
  rw [hellinger_sq_eq_sum_add_sub_two_bhattacharyya p q hp.1 hq.1, hp.2, hq.2]
  ring

/-- Pointwise square-root contraction: squaring the root gap cannot exceed the original
absolute gap. No sign hypothesis is needed because `Real.sqrt` vanishes on nonpositive inputs. -/
theorem sq_sqrt_sub_sqrt_le_abs_sub (a b : ℝ) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · have habs :
          |a - b| =
            |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
        calc
          |a - b| = |Real.sqrt a ^ 2 - Real.sqrt b ^ 2| := by
            rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
          _ = |(Real.sqrt a - Real.sqrt b) *
              (Real.sqrt a + Real.sqrt b)| := by ring_nf
          _ = |Real.sqrt a - Real.sqrt b| *
              (Real.sqrt a + Real.sqrt b) := by
            rw [abs_mul,
              abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      have hroot :
          |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
        rw [abs_le]
        constructor <;> linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
      calc
        (Real.sqrt a - Real.sqrt b) ^ 2 =
            |Real.sqrt a - Real.sqrt b| ^ 2 := (sq_abs _).symm
        _ = |Real.sqrt a - Real.sqrt b| *
            |Real.sqrt a - Real.sqrt b| := by ring
        _ ≤ |Real.sqrt a - Real.sqrt b| *
            (Real.sqrt a + Real.sqrt b) :=
          mul_le_mul_of_nonneg_left hroot (abs_nonneg _)
        _ = |a - b| := habs.symm
    · have hb' : b ≤ 0 := le_of_not_ge hb
      rw [Real.sqrt_eq_zero_of_nonpos hb', sub_zero, Real.sq_sqrt ha,
        abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith
  · have ha' : a ≤ 0 := le_of_not_ge ha
    by_cases hb : 0 ≤ b
    · rw [Real.sqrt_eq_zero_of_nonpos ha',
        abs_of_nonpos (by linarith : a - b ≤ 0)]
      nlinarith [Real.sq_sqrt hb]
    · have hb' : b ≤ 0 := le_of_not_ge hb
      calc
        (Real.sqrt a - Real.sqrt b) ^ 2 = 0 := by
          rw [Real.sqrt_eq_zero_of_nonpos ha', Real.sqrt_eq_zero_of_nonpos hb']
          norm_num
        _ ≤ |a - b| := abs_nonneg _

/-- Half the squared Hellinger distance is bounded by total variation for arbitrary finite real
functions. Neither nonnegativity nor normalization is needed. -/
theorem hellinger_sq_div_two_le_total_variation
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    hellingerSq p q / 2 ≤ totalVariation p q := by
  rw [hellingerSq, totalVariation]
  have hsum :
      (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) ≤
        ∑ i, |p i - q i| := by
    apply Finset.sum_le_sum
    intro i _
    exact sq_sqrt_sub_sqrt_le_abs_sub (p i) (q i)
  nlinarith

/-- Restatement, not an independent bound: the frozen Bhattacharyya square inequality written
in squared-Hellinger coordinates. -/
theorem total_variation_sq_le_hellinger_sq_sub_quarter
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    totalVariation p q ^ 2 ≤
      hellingerSq p q - hellingerSq p q ^ 2 / 4 := by
  have hfrozen :=
    total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
  have hbridge := hellinger_sq_eq_two_sub p q hp hq
  calc
    totalVariation p q ^ 2 ≤ 1 - bhattacharyya p q ^ 2 := hfrozen
    _ = 2 * (1 - bhattacharyya p q) -
        (2 * (1 - bhattacharyya p q)) ^ 2 / 4 := by ring
    _ = hellingerSq p q - hellingerSq p q ^ 2 / 4 := by rw [hbridge]

/-- The lower bracket is strict for a point mass against the probability vector `(9/25, 16/25)`.
The Pythagorean-square coordinates make the square roots rational. -/
theorem hellinger_sq_lower_strict_witness :
    hellingerSq
        (fun b : Bool => if b then (1 : ℝ) else 0)
        (fun b : Bool => if b then (9 / 25 : ℝ) else 16 / 25) / 2 <
      totalVariation
        (fun b : Bool => if b then (1 : ℝ) else 0)
        (fun b : Bool => if b then (9 / 25 : ℝ) else 16 / 25) := by
  have hsqrt_nine : Real.sqrt (9 / 25 : ℝ) = 3 / 5 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have hsqrt_sixteen : Real.sqrt (16 / 25 : ℝ) = 4 / 5 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  norm_num [hellingerSq, totalVariation, Fintype.sum_bool,
    hsqrt_nine, hsqrt_sixteen]

end D5.S3.TotalVariation.Hellinger
