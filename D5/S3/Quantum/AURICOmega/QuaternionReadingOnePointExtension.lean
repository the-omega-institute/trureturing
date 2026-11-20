/- GID: D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-point extensions of the unit-quaternion reading are affine with a norm bound. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

/-! One-point extensions of the unit-quaternion reading.

Extend the unit quaternions with the reading `(1 + ⟪x, y⟫) / 2` by one new point whose readings
against the old points are `f x` and whose reading with itself is `d`. The finite Gram forms of
the extended reading are `d * t ^ 2 + 2 * t * ∑ c i * f (x i) + ∑ c i * c j * kappa (x i) (x j)`,
and the Gram form of the old points is half of `(∑ c i) ^ 2 + ‖∑ c i • x i‖ ^ 2`.

If `f x = (a + ⟪b, x⟫) / √2` with `a ^ 2 + ‖b‖ ^ 2 ≤ d`, each extended form is a sum of two
squares and a nonnegative multiple of `t ^ 2`. Conversely, the combination of `y` with the five
points `1, -1, i, j, k` that has total weight zero and weighted sum zero has Gram form zero, so
nonnegativity in `t` forces the readings to be compatible with this linear relation, which makes
`f` affine in the quaternion coordinates; the combination of the five points with total weight
`-√2 * a` and weighted sum `-√2 • b` then gives `a ^ 2 + ‖b‖ ^ 2 ≤ d`.

If the extended reading is realized by unit vectors in Euclidean five-space, the old points
already span that space, since the reading has feature rank at least five. The new vector is a
combination of old ones, and the Cauchy-Schwarz inequality for its readings gives
`a ^ 2 + ‖b‖ ^ 2 ≥ 1`. The readings are nonnegative exactly when `‖b‖ ≤ a`, the minimum of
`⟪b, x⟫` on unit quaternions being `-‖b‖`. Under both conditions, a reading zero or a reading one
is an equality case of the Cauchy-Schwarz inequality, which forces `a = ‖b‖ = 1 / √2` and `b` to
be a multiple of a unit quaternion; the readings are then those of that unit quaternion. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

/-- The reading of the unit-quaternion model extended by one new point, read by `f` against the
old points, is the Gram kernel of a map into Euclidean `r`-space with the new point of norm one. -/
def HasOnePointFeatureRank (f : unitary ℍ[ℝ] → ℝ) (r : ℕ) : Prop :=
  ∃ φ : Option (unitary ℍ[ℝ]) → EuclideanSpace ℝ (Fin r),
    (∀ x y, quaternionModel.kappa x y = ⟪φ (some x), φ (some y)⟫_ℝ) ∧
      (∀ x, f x = ⟪φ (some x), φ none⟫_ℝ) ∧ ‖φ none‖ = 1

/-- The Gram form of the reading on finitely many unit quaternions is half the sum of the squared
total weight and the squared norm of the weighted sum. -/
private lemma gram_eq {ι : Type*} (s : Finset ι) (c : ι → ℝ) (x : ι → unitary ℍ[ℝ]) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * quaternionModel.kappa (x i) (x j) =
      ((∑ i ∈ s, c i) ^ 2 + ‖∑ i ∈ s, c i • (x i : ℍ[ℝ])‖ ^ 2) / 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  change c i * c j * ((1 + ⟪(x i : ℍ[ℝ]), (x j : ℍ[ℝ])⟫_ℝ) / 2) = _
  ring

/-- Weighted sums of affine readings are affine in the total weight and the weighted sum. -/
private lemma sum_mul_affine {ι : Type*} (s : Finset ι) (c : ι → ℝ) (x : ι → unitary ℍ[ℝ])
    (a : ℝ) (b : ℍ[ℝ]) :
    ∑ i ∈ s, c i * ((a + ⟪b, (x i : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) =
      (a * ∑ i ∈ s, c i + ⟪b, ∑ i ∈ s, c i • (x i : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := by
  rw [inner_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]
  ring

/-- The extended Gram form of an affine reading with `a ^ 2 + ‖b‖ ^ 2 ≤ d` is half a sum of two
squares plus `t ^ 2 * (d - a ^ 2 - ‖b‖ ^ 2)`. -/
private lemma affine_form_nonneg (a d t s : ℝ) (b q : ℍ[ℝ]) (h : a ^ 2 + ‖b‖ ^ 2 ≤ d) :
    0 ≤ d * t ^ 2 + 2 * t * ((a * s + ⟪b, q⟫_ℝ) / Real.sqrt 2) + (s ^ 2 + ‖q‖ ^ 2) / 2 := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hq : ‖q + (Real.sqrt 2 * t) • b‖ ^ 2 =
      ‖q‖ ^ 2 + 2 * (Real.sqrt 2 * t) * ⟪b, q⟫_ℝ + 2 * t ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      mul_pow, hσ, real_inner_comm]
    ring
  have e : 2 * t * ((a * s + ⟪b, q⟫_ℝ) / Real.sqrt 2) =
      Real.sqrt 2 * t * (a * s + ⟪b, q⟫_ℝ) := by
    rw [mul_div_assoc', div_eq_iff hσ0.ne']
    linear_combination (-(t * (a * s + ⟪b, q⟫_ℝ))) * hσ
  have key : d * t ^ 2 + Real.sqrt 2 * t * (a * s + ⟪b, q⟫_ℝ) + (s ^ 2 + ‖q‖ ^ 2) / 2 =
      ((s + Real.sqrt 2 * t * a) ^ 2 + ‖q + (Real.sqrt 2 * t) • b‖ ^ 2) / 2 +
        t ^ 2 * (d - (a ^ 2 + ‖b‖ ^ 2)) := by
    rw [hq]
    linear_combination (-(t ^ 2 * a ^ 2) / 2) * hσ
  rw [e, key]
  exact add_nonneg (by positivity) (mul_nonneg (sq_nonneg t) (sub_nonneg.mpr h))

/-- If every extended Gram form is nonnegative, a combination of old points with total weight
zero and weighted sum zero has total reading zero against the new point. -/
private lemma sum_mul_eq_zero (f : unitary ℍ[ℝ] → ℝ) (d : ℝ)
    (hH : ∀ (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ),
      0 ≤ d * t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
        ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j))
    {n : ℕ} (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (hs : ∑ i, c i = 0)
    (hq : ∑ i, c i • (x i : ℍ[ℝ]) = 0) : ∑ i, c i * f (x i) = 0 := by
  set L := ∑ i, c i * f (x i)
  have hD : 0 < |d| + 1 := by positivity
  have h := hH n x c (-L / (|d| + 1))
  rw [gram_eq, hs, hq, norm_zero] at h
  have e : d * (-L / (|d| + 1)) ^ 2 + 2 * (-L / (|d| + 1)) * L + ((0 : ℝ) ^ 2 + 0 ^ 2) / 2 =
      (d * L ^ 2 - 2 * L ^ 2 * (|d| + 1)) / (|d| + 1) ^ 2 := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity), zero_mul] at h
  have hL : L ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self d)) (sq_nonneg L),
      mul_nonneg (abs_nonneg d) (sq_nonneg L)]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hL (sq_nonneg L))

/-- The five unit quaternions `1, -1, i, j, k`. -/
private def pts : Fin 5 → unitary ℍ[ℝ] := ![1, -1, unitI, unitJ, unitI * unitJ]

/-- Coefficients on `1, -1, i, j, k` with total weight `s` and weighted sum `q`. -/
private def coef (s : ℝ) (q : ℍ[ℝ]) : Fin 5 → ℝ :=
  ![(s + q.re - q.imI - q.imJ - q.imK) / 2, (s - q.re - q.imI - q.imJ - q.imK) / 2, q.imI, q.imJ,
    q.imK]

private lemma sum_coef (s : ℝ) (q : ℍ[ℝ]) : ∑ k, coef s q k = s := by
  simp [Fin.sum_univ_five, coef]
  ring

private lemma sum_coef_smul (s : ℝ) (q : ℍ[ℝ]) : ∑ k, coef s q k • (pts k : ℍ[ℝ]) = q := by
  rw [Fin.sum_univ_five]
  ext
  · simp [coef, pts, unitI, unitJ, Unitary.coe_neg]
    ring
  all_goals simp [coef, pts, unitI, unitJ, Unitary.coe_neg]

/-- A unit quaternion pointing along any quaternion: `b = ‖b‖ • u`. -/
private lemma exists_unit_smul (b : ℍ[ℝ]) : ∃ u : unitary ℍ[ℝ], b = ‖b‖ • (u : ℍ[ℝ]) := by
  by_cases hb : b = 0
  · exact ⟨1, by simp [hb]⟩
  · have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    refine ⟨⟨‖b‖⁻¹ • b, ?_⟩, ?_⟩
    · rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm, norm_smul,
        norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · change b = ‖b‖ • (‖b‖⁻¹ • b)
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- The readings `(a + ⟪b, x⟫) / √2` on the unit quaternions are nonnegative exactly when
`‖b‖ ≤ a`. -/
private lemma forall_nonneg_iff (a : ℝ) (b : ℍ[ℝ]) :
    (∀ x : unitary ℍ[ℝ], 0 ≤ (a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) ↔ ‖b‖ ≤ a := by
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  constructor
  · intro h
    obtain ⟨u, hu⟩ := exists_unit_smul b
    have h' := h (-u)
    rw [Unitary.coe_neg, inner_neg_right, le_div_iff₀ hσ0, zero_mul] at h'
    have hbu : ⟪b, (u : ℍ[ℝ])⟫_ℝ = ‖b‖ := by
      conv_lhs => rw [hu]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, CStarRing.norm_coe_unitary]
      ring
    linarith
  · intro h x
    have hx := abs_real_inner_le_norm b (x : ℍ[ℝ])
    rw [CStarRing.norm_coe_unitary, mul_one] at hx
    exact div_nonneg (by linarith [neg_abs_le ⟪b, (x : ℍ[ℝ])⟫_ℝ]) hσ0.le

/-- One-point extensions of the unit-quaternion reading. Extending the reading by one point with
self-reading `d` keeps every finite Gram form nonnegative exactly when the new readings are
`(a + ⟪b, x⟫) / √2` with `a ^ 2 + ‖b‖ ^ 2 ≤ d`. -/
theorem onePointExtension_iff (f : unitary ℍ[ℝ] → ℝ) (d : ℝ) :
    (∀ (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ),
        0 ≤ d * t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
          ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j)) ↔
      ∃ (a : ℝ) (b : ℍ[ℝ]), a ^ 2 + ‖b‖ ^ 2 ≤ d ∧
        ∀ x : unitary ℍ[ℝ], f x = (a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  constructor
  · intro hH
    -- the readings satisfy the linear relation of `y` with `1, -1, i, j, k`
    have hrep : ∀ y : unitary ℍ[ℝ], f y = ∑ k, coef 1 (y : ℍ[ℝ]) k * f (pts k) := by
      intro y
      have h := sum_mul_eq_zero f d hH (Fin.cons y pts) (Fin.cons (-1) (coef 1 (y : ℍ[ℝ])))
        (by rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ, sum_coef]; ring)
        (by
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, sum_coef_smul]
          rw [neg_one_smul, neg_add_cancel])
      rw [Fin.sum_univ_succ] at h
      simp only [Fin.cons_zero, Fin.cons_succ] at h
      linarith
    obtain ⟨a, b, hab⟩ : ∃ (a : ℝ) (b : ℍ[ℝ]), ∀ y : unitary ℍ[ℝ],
        f y = (a + ⟪b, (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := by
      refine ⟨Real.sqrt 2 * ((f (pts 0) + f (pts 1)) / 2),
        Real.sqrt 2 • ⟨(f (pts 0) - f (pts 1)) / 2, f (pts 2) - (f (pts 0) + f (pts 1)) / 2,
          f (pts 3) - (f (pts 0) + f (pts 1)) / 2, f (pts 4) - (f (pts 0) + f (pts 1)) / 2⟩,
        fun y => ?_⟩
      rw [real_inner_smul_left, ← mul_add, mul_div_cancel_left₀ _ hσ0.ne', hrep y,
        inner_eq_components, Fin.sum_univ_five]
      simp [coef]
      ring
    refine ⟨a, b, ?_, hab⟩
    -- the combination with total weight `-√2 * a` and weighted sum `-√2 • b`
    have hb := hH 5 pts (coef (-(Real.sqrt 2 * a)) (-(Real.sqrt 2 • b))) 1
    simp only [hab] at hb
    rw [sum_mul_affine, gram_eq, sum_coef, sum_coef_smul, inner_neg_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hσ]
      at hb
    have e1 : (a * -(Real.sqrt 2 * a) + -(Real.sqrt 2 * ‖b‖ ^ 2)) / Real.sqrt 2 =
        -(a ^ 2 + ‖b‖ ^ 2) := by
      field_simp
      ring
    have e2 : (-(Real.sqrt 2 * a)) ^ 2 = 2 * a ^ 2 := by rw [neg_sq, mul_pow, hσ]
    rw [e1, e2] at hb
    linarith
  · rintro ⟨a, b, hd, hf⟩ n x c t
    have hs : ∑ i, c i * f (x i) = ∑ i, c i * ((a + ⟪b, (x i : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) :=
      Finset.sum_congr rfl fun i _ => by rw [hf]
    rw [hs, sum_mul_affine, gram_eq]
    exact affine_form_nonneg a d t _ b _ hd

/-- A realized one-point extension has nonnegative extended Gram forms with `d = ‖z‖ ^ 2`. -/
private lemma form_nonneg_of_realization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P : unitary ℍ[ℝ] → E) (z : E)
    (hP : ∀ x y, quaternionModel.kappa x y = ⟪P x, P y⟫_ℝ) (f : unitary ℍ[ℝ] → ℝ)
    (hf : ∀ x, f x = ⟪P x, z⟫_ℝ) (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ) :
    0 ≤ ‖z‖ ^ 2 * t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
      ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j) := by
  have h1 : ⟪z, ∑ i, c i • P (x i)⟫_ℝ = ∑ i, c i * f (x i) := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right, real_inner_comm, hf]
  have h2 : ‖∑ i, c i • P (x i)‖ ^ 2 =
      ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right, hP]
    ring
  have h3 := sq_nonneg ‖t • z + ∑ i, c i • P (x i)‖
  rw [norm_add_sq_real, norm_smul, real_inner_smul_left, h1, h2, mul_pow, Real.norm_eq_abs,
    sq_abs] at h3
  linarith

/-- In Euclidean five-space, a unit vector whose readings against a realization of the
unit-quaternion reading are `(a + ⟪b, x⟫) / √2` has `a ^ 2 + ‖b‖ ^ 2 ≥ 1`. -/
private lemma one_le_of_five (P : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin 5))
    (z : EuclideanSpace ℝ (Fin 5)) (hP : ∀ x y, quaternionModel.kappa x y = ⟪P x, P y⟫_ℝ)
    (hz : ‖z‖ = 1) (a : ℝ) (b : ℍ[ℝ])
    (hab : ∀ x, ⟪P x, z⟫_ℝ = (a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) : 1 ≤ a ^ 2 + ‖b‖ ^ 2 := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set V := Submodule.span ℝ (Set.range P)
  have h5 : 5 ≤ Module.finrank ℝ V :=
    five_le_of_hasFeatureRank quaternionModel quaternionModel_noncommutative
      quaternionModel_chainConnected _
      ⟨fun x => (stdOrthonormalBasis ℝ V).repr ⟨P x, Submodule.subset_span ⟨x, rfl⟩⟩,
        fun x y => by rw [LinearIsometryEquiv.inner_map_map, Submodule.coe_inner, hP]⟩
  have hV : V = ⊤ := Submodule.eq_top_of_finrank_eq
    (le_antisymm (Submodule.finrank_le V) (by rw [finrank_euclideanSpace_fin]; exact h5))
  have hzV : z ∈ V := by
    rw [hV]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hzV
  simp only [Finsupp.sum] at hc
  set s := c.support
  have h1 : ∑ x ∈ s, ∑ y ∈ s, c x * c y * quaternionModel.kappa x y = 1 := by
    have e : ∑ x ∈ s, ∑ y ∈ s, c x * c y * quaternionModel.kappa x y = ⟪z, z⟫_ℝ := by
      rw [← hc, sum_inner]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right, hP]
      ring
    rw [e, real_inner_self_eq_norm_sq, hz, one_pow]
  have h2 : ∑ x ∈ s, c x * ((a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) = 1 := by
    have e : ∑ x ∈ s, c x * ((a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) =
        ⟪∑ x ∈ s, c x • P x, z⟫_ℝ := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun x _ => by rw [real_inner_smul_left, hab]
    rw [e, hc, real_inner_self_eq_norm_sq, hz, one_pow]
  have g1 := gram_eq s c (fun x => x)
  have g2 := sum_mul_affine s c (fun x => x) a b
  rw [h1] at g1
  rw [h2] at g2
  set S := ∑ x ∈ s, c x
  set Q := ∑ x ∈ s, c x • (x : ℍ[ℝ])
  have hcs := real_inner_le_norm b Q
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have h3 : Real.sqrt 2 ≤ a * S + ‖b‖ * ‖Q‖ := by
    have : a * S + ⟪b, Q⟫_ℝ = Real.sqrt 2 := by
      field_simp at g2
      linarith
    linarith
  have h4 : 2 ≤ (a * S + ‖b‖ * ‖Q‖) ^ 2 := by
    rw [← hσ]
    exact pow_le_pow_left₀ hσ0.le h3 2
  have h5 : (a ^ 2 + ‖b‖ ^ 2) * (S ^ 2 + ‖Q‖ ^ 2) =
      (a * S + ‖b‖ * ‖Q‖) ^ 2 + (a * ‖Q‖ - ‖b‖ * S) ^ 2 := by ring
  rw [show S ^ 2 + ‖Q‖ ^ 2 = 2 by linarith] at h5
  nlinarith [sq_nonneg (a * ‖Q‖ - ‖b‖ * S)]

/-- The vector `(a, re b, imI b, imJ b, imK b)` of Euclidean five-space. -/
private def vecAB (a : ℝ) (b : ℍ[ℝ]) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![a, b.re, b.imI, b.imJ, b.imK]

private lemma inner_feature_vecAB (a : ℝ) (b q : ℍ[ℝ]) :
    ⟪feature q, vecAB a b⟫_ℝ = (a + ⟪b, q⟫_ℝ) / Real.sqrt 2 := by
  rw [feature, vecAB, real_inner_smul_left, EuclideanSpace.inner_toLp_toLp, inner_eq_components]
  simp only [dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.cons_val_succ, star_trivial]
  ring

private lemma norm_vecAB (a : ℝ) (b : ℍ[ℝ]) (h : a ^ 2 + ‖b‖ ^ 2 = 1) : ‖vecAB a b‖ = 1 := by
  have h2 : ‖vecAB a b‖ ^ 2 = 1 := by
    have e : ‖vecAB a b‖ ^ 2 = a ^ 2 + ⟪b, b⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq, vecAB, EuclideanSpace.inner_toLp_toLp,
        inner_eq_components]
      simp only [dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
        Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Matrix.cons_val_succ, star_trivial]
      ring
    rw [e, real_inner_self_eq_norm_sq, h]
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]

/-- The nonnegative one-point extensions of the unit-quaternion reading of feature rank five are
exactly the readings `(a + ⟪b, x⟫) / √2` with `‖b‖ ≤ a` and `a ^ 2 + ‖b‖ ^ 2 = 1`. -/
theorem hasOnePointFeatureRank_five_iff (f : unitary ℍ[ℝ] → ℝ) :
    (HasOnePointFeatureRank f 5 ∧ ∀ x, 0 ≤ f x) ↔
      ∃ (a : ℝ) (b : ℍ[ℝ]), ‖b‖ ≤ a ∧ a ^ 2 + ‖b‖ ^ 2 = 1 ∧
        ∀ x : unitary ℍ[ℝ], f x = (a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := by
  constructor
  · rintro ⟨⟨φ, hk, hf, hn⟩, h0⟩
    obtain ⟨a, b, hle, hab⟩ := (onePointExtension_iff f 1).mp fun n x c t => by
      have h := form_nonneg_of_realization (fun x => φ (some x)) (φ none) hk f hf n x c t
      rwa [hn, one_pow] at h
    refine ⟨a, b, (forall_nonneg_iff a b).mp fun x => hab x ▸ h0 x,
      le_antisymm hle (one_le_of_five _ _ hk hn a b fun x => (hf x).symm.trans (hab x)), hab⟩
  · rintro ⟨a, b, hba, hab, hf⟩
    refine ⟨⟨fun o => o.elim (vecAB a b) fun x => feature x, fun x y => (inner_feature x y).symm,
      fun x => (hf x).trans (inner_feature_vecAB a b x).symm, norm_vecAB a b hab⟩, fun x => ?_⟩
    rw [hf x]
    exact (forall_nonneg_iff a b).mpr hba x

/-- A nonnegative one-point extension of feature rank five reads zero against some old point
exactly when it reads one against some old point, exactly when it is the reading of an old
point. -/
theorem tfae_eq_kappa_of_hasOnePointFeatureRank_five (f : unitary ℍ[ℝ] → ℝ)
    (hf : HasOnePointFeatureRank f 5) (h0 : ∀ x, 0 ≤ f x) :
    List.TFAE [∃ x₁, f x₁ = 0, ∃ x₁, f x₁ = 1,
      ∃ x₀, ∀ x, f x = quaternionModel.kappa x x₀] := by
  obtain ⟨a, b, hba, hab, hfab⟩ := (hasOnePointFeatureRank_five_iff f).mp ⟨hf, h0⟩
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hcs : ∀ x : unitary ℍ[ℝ], |⟪b, (x : ℍ[ℝ])⟫_ℝ| ≤ ‖b‖ := fun x => by
    have h := abs_real_inner_le_norm b (x : ℍ[ℝ])
    rwa [CStarRing.norm_coe_unitary, mul_one] at h
  -- in both equality cases `a = ‖b‖ = 1 / √2`, that is `2 * a = √2`
  have half : ∀ (x₁ : unitary ℍ[ℝ]) (ε : ℝ), ε ^ 2 = 1 → ‖b‖ = a →
      ⟪b, (x₁ : ℍ[ℝ])⟫_ℝ = ε * ‖b‖ → b = (ε * ‖b‖) • (x₁ : ℍ[ℝ]) ∧ 2 * a = Real.sqrt 2 := by
    intro x₁ ε hε hba' hbx
    have ha0 : 0 ≤ a := hba' ▸ norm_nonneg b
    have h2a : (2 * a) ^ 2 = Real.sqrt 2 ^ 2 := by rw [hσ]; nlinarith [hab, hba']
    refine ⟨?_, (pow_left_inj₀ (by positivity) hσ0.le two_ne_zero).mp h2a⟩
    have hz : ‖b - (ε * ‖b‖) • (x₁ : ℍ[ℝ])‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, real_inner_smul_right, hbx, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, CStarRing.norm_coe_unitary]
      linear_combination (-‖b‖ ^ 2) * hε
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz))
  have reading : ∀ (x₀ : unitary ℍ[ℝ]), b = a • (x₀ : ℍ[ℝ]) → 2 * a = Real.sqrt 2 →
      ∀ x, f x = quaternionModel.kappa x x₀ := by
    intro x₀ hb h2a x
    rw [hfab, hb, real_inner_smul_left, real_inner_comm]
    change _ = (1 + ⟪(x : ℍ[ℝ]), (x₀ : ℍ[ℝ])⟫_ℝ) / 2
    rw [div_eq_div_iff hσ0.ne' two_ne_zero, ← h2a]
    ring
  tfae_have 1 → 3 := by
    rintro ⟨x₁, hx₁⟩
    rw [hfab, div_eq_zero_iff, or_iff_left hσ0.ne'] at hx₁
    have hle : a ≤ ‖b‖ := by linarith [neg_abs_le ⟪b, (x₁ : ℍ[ℝ])⟫_ℝ, hcs x₁]
    have hba' : ‖b‖ = a := le_antisymm hba hle
    obtain ⟨hb, h2a⟩ := half x₁ (-1) (by norm_num) hba' (by linarith)
    refine ⟨-x₁, reading (-x₁) ?_ h2a⟩
    rw [hb, Unitary.coe_neg, hba', smul_neg, neg_one_mul, neg_smul]
  tfae_have 2 → 3 := by
    rintro ⟨x₁, hx₁⟩
    rw [hfab, div_eq_one_iff_eq hσ0.ne'] at hx₁
    have hle := le_abs_self ⟪b, (x₁ : ℍ[ℝ])⟫_ℝ
    have hb1 := hcs x₁
    have hba' : ‖b‖ = a := by
      have h1 : Real.sqrt 2 ≤ a + ‖b‖ := by linarith
      have h2 : 2 ≤ (a + ‖b‖) ^ 2 := by
        rw [← hσ]
        exact pow_le_pow_left₀ hσ0.le h1 2
      nlinarith [sq_nonneg (a - ‖b‖)]
    have h2a : 2 * a = Real.sqrt 2 := by
      have ha0 : 0 ≤ a := hba' ▸ norm_nonneg b
      have h2a : (2 * a) ^ 2 = Real.sqrt 2 ^ 2 := by rw [hσ]; nlinarith [hab, hba']
      exact (pow_left_inj₀ (by positivity) hσ0.le two_ne_zero).mp h2a
    obtain ⟨hb, -⟩ := half x₁ 1 (by norm_num) hba' (by rw [one_mul]; linarith)
    exact ⟨x₁, reading x₁ (by rw [hb, one_mul, hba']) h2a⟩
  tfae_have 3 → 1 := by
    rintro ⟨x₀, hx₀⟩
    refine ⟨-x₀, ?_⟩
    rw [hx₀]
    change (1 + ⟪((-x₀ : unitary ℍ[ℝ]) : ℍ[ℝ]), (x₀ : ℍ[ℝ])⟫_ℝ) / 2 = 0
    rw [Unitary.coe_neg, inner_neg_left, real_inner_self_eq_norm_sq, CStarRing.norm_coe_unitary]
    norm_num
  tfae_have 3 → 2 := by
    rintro ⟨x₀, hx₀⟩
    exact ⟨x₀, by rw [hx₀, quaternionModel.kappa_self]⟩
  tfae_finish

end D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
