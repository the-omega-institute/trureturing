/- GID: D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact attained orientation minimum on the complex rank-two two-mode CAR orbit. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The public rank-two reduction supplies a scalar comparison
plane, while the explicit minimizing projection attains the twoModeMinimum
and the public exact-minimum theorem packages the lower bound and witness.
-/

import D5.S3.Quantum.Semigroups.WuTwoLevelOrientationMinimum
import D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker

/-! Exact orientation minimization on the complex rank-two orbit of the two CAR modes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Semigroups.WuTwoModeRankTwoAttainedOrientation

open WuCubicOperatorBridge (Mat)
open WuTwoModeCliffordPluecker
open _root_.WuTwoLevelOrientationMinimum

local notation "planeInner" => WuTwoModeCliffordPluecker.inner

/-- Twice the weighted crossing cost, in the Clifford coordinates. -/
def weightedCost (A₁ A₂ : ℝ) (p : Coordinates) : ℝ :=
  ∑ k : Edge, (A₁ * (modeDegree 0 k : ℝ) + A₂ * (modeDegree 1 k : ℝ)) * p k ^ 2

private def vertexWeight (A₁ A₂ : ℝ) : Fin 6 → ℝ :=
  ![A₁, A₁, A₂, A₂, 2 * min A₁ A₂, 0]

private def blockOne (u : Fin 6 → ℝ) : ℝ := u 0 ^ 2 + u 1 ^ 2
private def blockTwo (u : Fin 6 → ℝ) : ℝ := u 2 ^ 2 + u 3 ^ 2

private theorem inner_self_blocks (u : Fin 6 → ℝ) :
    planeInner u u = blockOne u + blockTwo u + u 4 ^ 2 + u 5 ^ 2 := by
  simp [WuTwoModeCliffordPluecker.inner, blockOne, blockTwo, Fin.sum_univ_succ]
  ring

private theorem inner_comm (u v : Fin 6 → ℝ) : planeInner u v = planeInner v u := by
  unfold WuTwoModeCliffordPluecker.inner
  exact Finset.sum_congr rfl fun i _ => mul_comm (u i) (v i)

private theorem inner_combination (u v : Fin 6 → ℝ) (a b c d : ℝ) :
    planeInner (fun i => a * u i + b * v i) (fun i => c * u i + d * v i) =
      a * c * planeInner u u + a * d * planeInner u v +
        b * c * planeInner v u + b * d * planeInner v v := by
  calc
    _ = ∑ i : Fin 6, (a * c * (u i * u i) + a * d * (u i * v i) +
        b * c * (v i * u i) + b * d * (v i * v i)) := by
      unfold WuTwoModeCliffordPluecker.inner
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [WuTwoModeCliffordPluecker.inner, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Rotate an oriented orthonormal pair so its first vector has sixth coordinate zero. -/
theorem wedge_with_sixth_zero {p : Coordinates}
    (hn : sqNorm p = 1) (hp : ∀ k, pluecker p k = 0) :
    ∃ u v : Fin 6 → ℝ, planeInner u u = 1 ∧ planeInner v v = 1 ∧ planeInner u v = 0 ∧
      u 5 = 0 ∧ wedge u v = p := by
  obtain ⟨u, v, hu, hv, huv, hw⟩ := (unit_pluecker_iff p).mp ⟨hn, hp⟩
  by_cases h : u 5 = 0
  · exact ⟨u, v, hu, hv, huv, h, hw⟩
  have hu₅pos : 0 < u 5 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 h).symm
  have hp₅ : 0 < u 5 ^ 2 + v 5 ^ 2 :=
    add_pos_of_pos_of_nonneg hu₅pos (sq_nonneg _)
  let r := Real.sqrt (u 5 ^ 2 + v 5 ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 hp₅
  have hr_sq : r ^ 2 = u 5 ^ 2 + v 5 ^ 2 := Real.sq_sqrt hp₅.le
  let a := v 5 / r
  let b := -u 5 / r
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp only [a, b]
    field_simp [hr.ne']
    nlinarith only [hr_sq]
  let x : Fin 6 → ℝ := fun i => a * u i + b * v i
  let y : Fin 6 → ℝ := fun i => (-b) * u i + a * v i
  have hvu : planeInner v u = 0 := (inner_comm v u).trans huv
  have hx : planeInner x x = 1 := by
    dsimp only [x]
    rw [inner_combination u v a b a b, hu, hv, huv, hvu]
    nlinarith only [hab]
  have hy : planeInner y y = 1 := by
    dsimp only [y]
    rw [inner_combination u v (-b) a (-b) a, hu, hv, huv, hvu]
    nlinarith only [hab]
  have hxy : planeInner x y = 0 := by
    dsimp only [x, y]
    rw [inner_combination u v a b (-b) a, hu, hv, huv, hvu]
    ring
  have hx₅ : x 5 = 0 := by
    dsimp only [x, a, b]
    field_simp [hr.ne']
    ring
  refine ⟨x, y, hx, hy, hxy, hx₅, ?_⟩
  rw [← hw]
  funext k
  calc
    wedge x y k = (a ^ 2 + b ^ 2) * wedge u v k := by
      dsimp only [wedge, x, y]
      ring
    _ = wedge u v k := by rw [hab, one_mul]

private theorem row_sq_minors {u v : Fin 6 → ℝ}
    (hu : planeInner u u = 1) (hv : planeInner v v = 1) (huv : planeInner u v = 0) (i : Fin 6) :
    (∑ j : Fin 6, (u i * v j - u j * v i) ^ 2) = u i ^ 2 + v i ^ 2 := by
  calc
    _ = ∑ j : Fin 6,
        (u i ^ 2 * (v j * v j) + v i ^ 2 * (u j * u j) -
          (2 * u i * v i) * (u j * v j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = u i ^ 2 * planeInner v v + v i ^ 2 * planeInner u u - (2 * u i * v i) * planeInner u v := by
      simp only [WuTwoModeCliffordPluecker.inner, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hu, hv, huv]; ring

set_option maxHeartbeats 1000000 in
-- Expanding the edge sum and the two vertex sums before ring normalization needs extra heartbeats.
private theorem additive_wedge (t : Fin 6 → ℝ) {u v : Fin 6 → ℝ}
    (hu : planeInner u u = 1) (hv : planeInner v v = 1) (huv : planeInner u v = 0) :
    (∑ k : Edge, (t (edge k).1 + t (edge k).2) * wedge u v k ^ 2) =
      ∑ i : Fin 6, t i * (u i ^ 2 + v i ^ 2) := by
  calc
    _ = ∑ i : Fin 6, t i * (∑ j : Fin 6, (u i * v j - u j * v i) ^ 2) := by
      simp [edge, wedge, Fin.sum_univ_succ]
      ring
    _ = _ := by simp only [row_sq_minors hu hv huv]

private theorem vertex_weight_le (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (k : Edge) :
    vertexWeight A₁ A₂ (edge k).1 + vertexWeight A₁ A₂ (edge k).2 ≤
      A₁ * (modeDegree 0 k : ℝ) + A₂ * (modeDegree 1 k : ℝ) := by
  fin_cases k <;> norm_num [vertexWeight, edge, modeDegree] <;>
    linarith only [add_nonneg hA₁ hA₂, min_le_left A₁ A₂, min_le_right A₁ A₂]

def additiveCost (A₁ A₂ : ℝ) (u v : Fin 6 → ℝ) : ℝ :=
  A₁ * (blockOne u + blockOne v) + A₂ * (blockTwo u + blockTwo v) +
    2 * min A₁ A₂ * (u 4 ^ 2 + v 4 ^ 2)

private theorem sum_vertex_weight (A₁ A₂ : ℝ) (u v : Fin 6 → ℝ) :
    (∑ i : Fin 6, vertexWeight A₁ A₂ i * (u i ^ 2 + v i ^ 2)) =
      additiveCost A₁ A₂ u v := by
  simp [vertexWeight, additiveCost, blockOne, blockTwo, Fin.sum_univ_succ]
  ring

/-- The physical quadratic form dominates the additive vertex weights. -/
theorem additiveCost_le_weightedCost {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {u v : Fin 6 → ℝ} (hu : planeInner u u = 1) (hv : planeInner v v = 1)
    (huv : planeInner u v = 0) :
    additiveCost A₁ A₂ u v ≤ weightedCost A₁ A₂ (wedge u v) := by
  rw [← sum_vertex_weight, ← additive_wedge _ hu hv huv]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (vertex_weight_le A₁ A₂ hA₁ hA₂ k) (sq_nonneg _)

/-- Equality holds on the coordinate hyperplane excluding the fifth vertex. -/
theorem weightedCost_eq_additiveCost {A₁ A₂ : ℝ} {u v : Fin 6 → ℝ}
    (hu : planeInner u u = 1) (hv : planeInner v v = 1) (huv : planeInner u v = 0)
    (hu₄ : u 4 = 0) (hv₄ : v 4 = 0) :
    weightedCost A₁ A₂ (wedge u v) = additiveCost A₁ A₂ u v := by
  rw [← sum_vertex_weight, ← additive_wedge _ hu hv huv]
  unfold weightedCost
  apply Finset.sum_congr rfl
  intro k _
  fin_cases k <;> norm_num [vertexWeight, edge, modeDegree, wedge, hu₄, hv₄]
  all_goals exact Or.inl (by ring)

private theorem exists_signed_component {X Y z : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hz : z ^ 2 ≤ X * Y) :
    ∃ c : ℝ, Real.sqrt X * c = z ∧ c ^ 2 ≤ Y := by
  rcases eq_or_lt_of_le hX with hzero | hpos
  · have hz₀ : z = 0 := by
      have hsq : z ^ 2 ≤ 0 := by simpa [← hzero] using hz
      by_contra hne
      exact (pow_ne_zero 2 hne) (le_antisymm hsq (sq_nonneg z))
    exact ⟨0, by simp [hz₀], by simpa using hY⟩
  · let r := Real.sqrt X
    have hr : 0 < r := Real.sqrt_pos.2 hpos
    have hr_sq : r ^ 2 = X := Real.sq_sqrt hX
    refine ⟨z / r, ?_, ?_⟩
    · change r * (z / r) = z
      field_simp [hr.ne']
    · rw [div_pow]
      exact (div_le_iff₀' (pow_pos hr 2)).2 (by rwa [hr_sq])

/-- Real coordinates of the comparison plane. The signs of the occupations are
carried by the two components of the second vector. -/
def planeCoordinates (X₁ X₂ c₁ c₂ : ℝ) : Coordinates :=
  wedge ![Real.sqrt X₁, 0, Real.sqrt X₂, 0, 0, 0]
    ![0, c₁, 0, c₂, 0, Real.sqrt (1 - c₁ ^ 2 - c₂ ^ 2)]

theorem planeCoordinates_spec {A₁ A₂ X₁ X₂ c₁ c₂ : ℝ}
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hX : X₁ + X₂ = 1)
    (hc : c₁ ^ 2 + c₂ ^ 2 ≤ 1) :
    let p := planeCoordinates X₁ X₂ c₁ c₂
    sqNorm p = 1 ∧ (∀ k, pluecker p k = 0) ∧
      p 0 = Real.sqrt X₁ * c₁ ∧ p 9 = Real.sqrt X₂ * c₂ ∧
      weightedCost A₁ A₂ p = A₁ * (X₁ + c₁ ^ 2) + A₂ * (X₂ + c₂ ^ 2) := by
  let u : Fin 6 → ℝ := ![Real.sqrt X₁, 0, Real.sqrt X₂, 0, 0, 0]
  let v : Fin 6 → ℝ := ![0, c₁, 0, c₂, 0, Real.sqrt (1 - c₁ ^ 2 - c₂ ^ 2)]
  have hu : planeInner u u = 1 := by
    rw [inner_self_blocks]
    simpa [u, blockOne, blockTwo, Real.sq_sqrt hX₁, Real.sq_sqrt hX₂] using hX
  have hv : planeInner v v = 1 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - c₁ ^ 2 - c₂ ^ 2 by linarith only [hc])
    rw [inner_self_blocks]
    simp [v, blockOne, blockTwo, hs]
  have huv : planeInner u v = 0 := by
    simp [u, v, WuTwoModeCliffordPluecker.inner, Fin.sum_univ_succ]
  obtain ⟨hn, hp⟩ := (unit_pluecker_iff (wedge u v)).mpr ⟨u, v, hu, hv, huv, rfl⟩
  change sqNorm (wedge u v) = 1 ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hn, hp, ?_, ?_, ?_⟩
  · simp [planeCoordinates, wedge, edge]
  · simp [planeCoordinates, wedge, edge]
  · change weightedCost A₁ A₂ (wedge u v) = _
    rw [weightedCost_eq_additiveCost hu hv huv (by simp [u]) (by simp [v])]
    simp [additiveCost, blockOne, blockTwo, u, v, Real.sq_sqrt hX₁, Real.sq_sqrt hX₂]

/-- Reduce a unit Plücker form to a comparison plane of no greater cost,
preserving both signed occupation coordinates. -/
theorem wedge_reduction {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {p : Coordinates} (hn : sqNorm p = 1) (hp : ∀ k, pluecker p k = 0) :
    ∃ X₁ X₂ c₁ c₂ : ℝ,
      0 ≤ X₁ ∧ 0 ≤ X₂ ∧ X₁ + X₂ = 1 ∧ c₁ ^ 2 + c₂ ^ 2 ≤ 1 ∧
      Real.sqrt X₁ * c₁ = p 0 ∧ Real.sqrt X₂ * c₂ = p 9 ∧
      A₁ * (X₁ + c₁ ^ 2) + A₂ * (X₂ + c₂ ^ 2) ≤ weightedCost A₁ A₂ p := by
  obtain ⟨u, v, hu, hv, huv, hu₅, hw⟩ := wedge_with_sixth_zero hn hp
  have hmass : blockOne u + blockTwo u + u 4 ^ 2 = 1 := by
    simpa [inner_self_blocks, hu₅] using hu
  have hmass' : blockOne v + blockTwo v ≤ 1 := by
    rw [inner_self_blocks] at hv
    linarith only [hv, sq_nonneg (v 4), sq_nonneg (v 5)]
  have hbudget := additiveCost_le_weightedCost hA₁ hA₂ hu hv huv
  rw [hw] at hbudget
  obtain ⟨X₁, X₂, hX₁, hX₂, hX, hcost⟩ :
      ∃ X₁ X₂ : ℝ, blockOne u ≤ X₁ ∧ blockTwo u ≤ X₂ ∧ X₁ + X₂ = 1 ∧
        A₁ * X₁ + A₂ * X₂ ≤
          A₁ * blockOne u + A₂ * blockTwo u + 2 * min A₁ A₂ * u 4 ^ 2 := by
    rcases le_total A₁ A₂ with h | h
    · refine ⟨blockOne u + u 4 ^ 2, blockTwo u, ?_, le_rfl, ?_, ?_⟩
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · linarith only [hmass]
      · rw [min_eq_left h]
        nlinarith only [mul_nonneg hA₁ (sq_nonneg (u 4))]
    · refine ⟨blockOne u, blockTwo u + u 4 ^ 2, le_rfl, ?_, ?_, ?_⟩
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · linarith only [hmass]
      · rw [min_eq_right h]
        nlinarith only [mul_nonneg hA₂ (sq_nonneg (u 4))]
  have hX₁₀ : 0 ≤ X₁ := (show 0 ≤ blockOne u by unfold blockOne; positivity).trans hX₁
  have hX₂₀ : 0 ≤ X₂ := (show 0 ≤ blockTwo u by unfold blockTwo; positivity).trans hX₂
  have hY₁ : 0 ≤ blockOne v := by unfold blockOne; positivity
  have hY₂ : 0 ≤ blockTwo v := by unfold blockTwo; positivity
  have hd₁ : p 0 ^ 2 ≤ blockOne u * blockOne v := by
    rw [← hw]
    simpa [wedge, edge, blockOne] using
      (real_two_plane_determinant_bound (u₁ := u 0) (u₂ := u 1) (v₁ := v 0) (v₂ := v 1))
  have hd₂ : p 9 ^ 2 ≤ blockTwo u * blockTwo v := by
    rw [← hw]
    simpa [wedge, edge, blockTwo] using
      (real_two_plane_determinant_bound (u₁ := u 2) (u₂ := u 3) (v₁ := v 2) (v₂ := v 3))
  obtain ⟨c₁, hc₁, hc₁sq⟩ := exists_signed_component hX₁₀ hY₁
    (hd₁.trans (mul_le_mul_of_nonneg_right hX₁ hY₁))
  obtain ⟨c₂, hc₂, hc₂sq⟩ := exists_signed_component hX₂₀ hY₂
    (hd₂.trans (mul_le_mul_of_nonneg_right hX₂ hY₂))
  have hcost₁ := mul_le_mul_of_nonneg_left hc₁sq hA₁
  have hcost₂ := mul_le_mul_of_nonneg_left hc₂sq hA₂
  have hmin : 0 ≤ min A₁ A₂ := le_min hA₁ hA₂
  have hfifth := mul_nonneg hmin (sq_nonneg (v 4))
  refine ⟨X₁, X₂, c₁, c₂, hX₁₀, hX₂₀, hX, ?_, hc₁, hc₂, ?_⟩
  · exact (add_le_add hc₁sq hc₂sq).trans hmass'
  · unfold additiveCost at hbudget
    nlinarith only [hbudget, hcost, hcost₁, hcost₂, hfifth]

/-- The signed contrast `Re Tr((2P-I) Zⱼ)/4` for the physical occupation matrix. -/
def occupationContrast (P : Mat) (j : Fin 2) : ℝ :=
  ((involution P * occupation j).trace.re / 4)

/-- Constant, thermal fields, and physical within-block jump costs. -/
def orientationValue (C A₁ A₂ B₁ B₂ : ℝ) (P : Mat) : ℝ :=
  C + B₁ * occupationContrast P 0 + B₂ * occupationContrast P 1 +
    A₁ * (1 - (within P 0).re) + A₂ * (1 - (within P 1).re)

private theorem projection_coordinates {P : Mat} {p : Coordinates}
    (hK : involution P = expand p) : coordinates (involution P) = p := by
  rw [hK, expand, coordinates_matrixOf]

private theorem occupationContrast_of_expand {P : Mat} {p : Coordinates}
    (hK : involution P = expand p) (j : Fin 2) :
    occupationContrast P j = p (![0, 9] j) := by
  unfold occupationContrast
  rw [hK, occupation_trace]

private theorem crossing_of_expand {P : Mat} {p : Coordinates}
    (hHerm : P.IsHermitian) (hP : P * P = P) (hRank : P.rank = 2)
    (hK : involution P = expand p) (j : Fin 2) :
    2 * (1 - (within P j).re) = ∑ k : Edge, (modeDegree j k : ℝ) * p k ^ 2 := by
  have h := within_quadratic hHerm hP hRank j
  dsimp only at h
  rwa [projection_coordinates hK] at h

private theorem weighted_crossing_of_expand {P : Mat} {p : Coordinates}
    (hHerm : P.IsHermitian) (hP : P * P = P) (hRank : P.rank = 2)
    (hK : involution P = expand p) (A₁ A₂ : ℝ) :
    2 * (A₁ * (1 - (within P 0).re) + A₂ * (1 - (within P 1).re)) =
      weightedCost A₁ A₂ p := by
  calc
    _ = A₁ * (∑ k : Edge, (modeDegree 0 k : ℝ) * p k ^ 2) +
        A₂ * (∑ k : Edge, (modeDegree 1 k : ℝ) * p k ^ 2) := by
      rw [← crossing_of_expand hHerm hP hRank hK 0, ← crossing_of_expand hHerm hP hRank hK 1]
      ring
    _ = _ := by
      simp only [weightedCost, add_mul, mul_assoc, Finset.mul_sum, Finset.sum_add_distrib]

/-- Every physical orientation has a comparison plane with identical signed occupations
and no greater weighted crossing cost. -/
theorem rank_two_plane_reduction {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {P : Mat} (hHerm : P.IsHermitian) (hP : P * P = P) (hRank : P.rank = 2) :
    ∃ X₁ X₂ c₁ c₂ : ℝ,
      0 ≤ X₁ ∧ 0 ≤ X₂ ∧ X₁ + X₂ = 1 ∧ c₁ ^ 2 + c₂ ^ 2 ≤ 1 ∧
      occupationContrast P 0 = Real.sqrt X₁ * c₁ ∧
      occupationContrast P 1 = Real.sqrt X₂ * c₂ ∧
      A₁ * (X₁ + c₁ ^ 2) + A₂ * (X₂ + c₂ ^ 2) ≤
        2 * (A₁ * (1 - (within P 0).re) + A₂ * (1 - (within P 1).re)) := by
  let p := coordinates (involution P)
  have hcert := rank_two_projection_certificate hHerm hP hRank
  have hK : involution P = expand p := hcert.1.trans (expand_eq_sum p).symm
  obtain ⟨X₁, X₂, c₁, c₂, hX₁, hX₂, hX, hc, hc₁, hc₂, hcost⟩ :=
    wedge_reduction hA₁ hA₂ hcert.2.1 hcert.2.2
  exact ⟨X₁, X₂, c₁, c₂, hX₁, hX₂, hX, hc,
    (occupationContrast_of_expand hK 0).trans hc₁.symm,
    (occupationContrast_of_expand hK 1).trans hc₂.symm,
    hcost.trans_eq (weighted_crossing_of_expand hHerm hP hRank hK A₁ A₂).symm⟩

/-- The explicit projection of the comparison plane. -/
def planeProjection (X₁ X₂ c₁ c₂ : ℝ) : Mat :=
  (1 / 2 : ℂ) • (expand (planeCoordinates X₁ X₂ c₁ c₂) + 1)

theorem planeProjection_spec {X₁ X₂ c₁ c₂ : ℝ}
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hX : X₁ + X₂ = 1)
    (hc : c₁ ^ 2 + c₂ ^ 2 ≤ 1) :
    let P := planeProjection X₁ X₂ c₁ c₂
    P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
      occupationContrast P 0 = Real.sqrt X₁ * c₁ ∧
      occupationContrast P 1 = Real.sqrt X₂ * c₂ ∧
      2 * (1 - (within P 0).re) = X₁ + c₁ ^ 2 ∧
      2 * (1 - (within P 1).re) = X₂ + c₂ ^ 2 := by
  let P := planeProjection X₁ X₂ c₁ c₂
  let p := planeCoordinates X₁ X₂ c₁ c₂
  have hgeom₀ := planeCoordinates_spec (A₁ := 1) (A₂ := 0) hX₁ hX₂ hX hc
  have hgeom₁ := planeCoordinates_spec (A₁ := 0) (A₂ := 1) hX₁ hX₂ hX hc
  obtain ⟨Q, hHerm, hQ, hRank, hK⟩ := projection_of_coordinates p hgeom₀.1 hgeom₀.2.1
  have hQP : Q = P := by
    change Q = (1 / 2 : ℂ) • (expand p + 1)
    rw [← hK]
    simp only [involution, sub_add_cancel, smul_smul]
    norm_num
  have hcost₀ := (weighted_crossing_of_expand hHerm hQ hRank hK 1 0).trans hgeom₀.2.2.2.2
  have hcost₁ := (weighted_crossing_of_expand hHerm hQ hRank hK 0 1).trans hgeom₁.2.2.2.2
  change P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
    occupationContrast P 0 = Real.sqrt X₁ * c₁ ∧
    occupationContrast P 1 = Real.sqrt X₂ * c₂ ∧
    2 * (1 - (within P 0).re) = X₁ + c₁ ^ 2 ∧
    2 * (1 - (within P 1).re) = X₂ + c₂ ^ 2
  rw [← hQP]
  exact ⟨hHerm, hQ, hRank,
    (occupationContrast_of_expand hK 0).trans hgeom₀.2.2.1,
    (occupationContrast_of_expand hK 1).trans hgeom₀.2.2.2.1,
    by simpa using hcost₀, by simpa using hcost₁⟩

/-- An explicit comparison projection preserves the two physical occupations and
can only decrease the orientation value, for any occupation fields. -/
theorem rank_two_projection_comparison {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {P : Mat} (hHerm : P.IsHermitian) (hP : P * P = P) (hRank : P.rank = 2) :
    ∃ X₁ X₂ c₁ c₂ : ℝ,
      let Q := planeProjection X₁ X₂ c₁ c₂
      Q.IsHermitian ∧ Q * Q = Q ∧ Q.rank = 2 ∧
        occupationContrast Q 0 = occupationContrast P 0 ∧
        occupationContrast Q 1 = occupationContrast P 1 ∧
        ∀ C B₁ B₂ : ℝ, orientationValue C A₁ A₂ B₁ B₂ Q ≤ orientationValue C A₁ A₂ B₁ B₂ P := by
  obtain ⟨X₁, X₂, c₁, c₂, hX₁, hX₂, hX, hc, hz₁, hz₂, hcost⟩ :=
    rank_two_plane_reduction hA₁ hA₂ hHerm hP hRank
  obtain ⟨hHerm', hQ, hRank', hz₁', hz₂', hcost₁, hcost₂⟩ := planeProjection_spec hX₁ hX₂ hX hc
  have hocc₁ := hz₁'.trans hz₁.symm
  have hocc₂ := hz₂'.trans hz₂.symm
  refine ⟨X₁, X₂, c₁, c₂, hHerm', hQ, hRank', hocc₁, hocc₂, ?_⟩
  intro C B₁ B₂
  unfold orientationValue
  rw [hocc₁, hocc₂]
  nlinarith only [hcost, congrArg (A₁ * ·) hcost₁, congrArg (A₂ * ·) hcost₂]

private theorem signed_field_lower (B X c : ℝ) (hX : 0 ≤ X) :
    -|B| * Real.sqrt (X * c ^ 2) ≤ B * (Real.sqrt X * c) := by
  have hs : Real.sqrt (X * c ^ 2) = |Real.sqrt X * c| := by
    calc
      _ = Real.sqrt ((Real.sqrt X * c) ^ 2) := by rw [mul_pow, Real.sq_sqrt hX]
      _ = _ := Real.sqrt_sq_eq_abs _
  calc
    _ = -|B * (Real.sqrt X * c)| := by rw [hs, abs_mul B (Real.sqrt X * c), neg_mul]
    _ ≤ _ := neg_abs_le _

/-- For every complex rank-two orthogonal projection, the physical orientation
value is bounded below by the scalar minimum with field magnitudes `|B₁|` and `|B₂|`. -/
theorem rank_two_orientation_lower {C A₁ A₂ B₁ B₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {P : Mat} (hHerm : P.IsHermitian) (hP : P * P = P) (hRank : P.rank = 2) :
    twoModeMinimum C A₁ A₂ |B₁| |B₂| ≤ orientationValue C A₁ A₂ B₁ B₂ P := by
  obtain ⟨X₁, X₂, c₁, c₂, hX₁, hX₂, hX, hc, hz₁, hz₂, hcost⟩ :=
    rank_two_plane_reduction hA₁ hA₂ hHerm hP hRank
  have hscalar := (twoMode_exact_minimum (C := C) hA₁ hA₂ (abs_nonneg B₁) (abs_nonneg B₂)).1
    X₁ X₂ (c₁ ^ 2) (c₂ ^ 2) hX₁ hX₂ (sq_nonneg _) (sq_nonneg _) hX hc
  apply hscalar.trans
  unfold productQuadratic orientationValue
  rw [hz₁, hz₂]
  nlinarith only [hcost, signed_field_lower B₁ X₁ c₁ hX₁, signed_field_lower B₂ X₂ c₂ hX₂]

/-- A projection polarized in mode `j`, with signed contrast `z`. -/
def axisProjection (j : Fin 2) (z : ℝ) : Mat :=
  if j = 0 then planeProjection 1 0 z 0 else planeProjection 0 1 0 z

theorem axisProjection_spec (j : Fin 2) {z : ℝ} (hz : z ^ 2 ≤ 1) :
    let P := axisProjection j z
    P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
      occupationContrast P j = z ∧ occupationContrast P (1 - j) = 0 ∧
      2 * (1 - (within P j).re) = 1 + z ^ 2 ∧
      2 * (1 - (within P (1 - j)).re) = 0 := by
  fin_cases j
  · have h := planeProjection_spec (X₁ := 1) (X₂ := 0) (c₁ := z) (c₂ := 0)
      (by norm_num) (by norm_num) (by norm_num) (by simpa using hz)
    change let P := planeProjection 1 0 z 0
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
        occupationContrast P 0 = z ∧ occupationContrast P 1 = 0 ∧
        2 * (1 - (within P 0).re) = 1 + z ^ 2 ∧
        2 * (1 - (within P 1).re) = 0
    simpa using h
  · obtain ⟨hHerm, hP, hRank, hocc₀, hocc₁, hcost₀, hcost₁⟩ :=
      planeProjection_spec (X₁ := 0) (X₂ := 1) (c₁ := 0) (c₂ := z)
        (by norm_num) (by norm_num) (by norm_num) (by simpa using hz)
    change let P := planeProjection 0 1 0 z
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
        occupationContrast P 1 = z ∧ occupationContrast P 0 = 0 ∧
        2 * (1 - (within P 1).re) = 1 + z ^ 2 ∧
        2 * (1 - (within P 0).re) = 0
    exact ⟨hHerm, hP, hRank, by simpa using hocc₁, by simpa using hocc₀,
      by simpa using hcost₁, by simpa using hcost₀⟩

/-- Choose the sign of the contrast to minimize the linear occupation field. -/
def favorableContrast (B u : ℝ) : ℝ := if 0 ≤ B then -u else u

private theorem favorableContrast_sq (B u : ℝ) : favorableContrast B u ^ 2 = u ^ 2 := by
  by_cases h : 0 ≤ B <;> simp [favorableContrast, h]

private theorem favorableContrast_field (B u : ℝ) : B * favorableContrast B u = -|B| * u := by
  by_cases h : 0 ≤ B
  · simp [favorableContrast, h, abs_of_nonneg h]
  · simp [favorableContrast, h, abs_of_nonpos (le_of_not_ge h)]

theorem orientationValue_axisProjection (C A₁ A₂ B₁ B₂ : ℝ) (j : Fin 2) {u : ℝ}
    (hu : u ^ 2 ≤ 1) :
    orientationValue C A₁ A₂ B₁ B₂ (axisProjection j (favorableContrast (![B₁, B₂] j) u)) =
      axisQuadratic C (![A₁, A₂] j) (abs (![B₁, B₂] j)) u := by
  have h := axisProjection_spec j (z := favorableContrast (![B₁, B₂] j) u)
    (by rwa [favorableContrast_sq])
  obtain ⟨_, _, _, hz, hother, hcross, hcrossOther⟩ := h
  rw [favorableContrast_sq] at hcross
  fin_cases j
  · let P := axisProjection 0 (favorableContrast B₁ u)
    change orientationValue C A₁ A₂ B₁ B₂ P = axisQuadratic C A₁ |B₁| u
    change occupationContrast P 0 = favorableContrast B₁ u at hz
    change occupationContrast P 1 = 0 at hother
    change 2 * (1 - (within P 0).re) = 1 + u ^ 2 at hcross
    change 2 * (1 - (within P 1).re) = 0 at hcrossOther
    unfold orientationValue axisQuadratic
    rw [hz, hother, favorableContrast_field]
    nlinarith only [congrArg (A₁ * ·) hcross, congrArg (A₂ * ·) hcrossOther]
  · let P := axisProjection 1 (favorableContrast B₂ u)
    change orientationValue C A₁ A₂ B₁ B₂ P = axisQuadratic C A₂ |B₂| u
    change occupationContrast P 1 = favorableContrast B₂ u at hz
    change occupationContrast P 0 = 0 at hother
    change 2 * (1 - (within P 1).re) = 1 + u ^ 2 at hcross
    change 2 * (1 - (within P 0).re) = 0 at hcrossOther
    unfold orientationValue axisQuadratic
    rw [hz, hother, favorableContrast_field]
    nlinarith only [congrArg (A₂ * ·) hcross, congrArg (A₁ * ·) hcrossOther]

/-- The minimizing physical mode, with the first mode chosen in a tie. -/
def minimizingMode (C A₁ A₂ B₁ B₂ : ℝ) : Fin 2 :=
  if axisMinimum C A₁ |B₁| ≤ axisMinimum C A₂ |B₂| then 0 else 1

/-- The explicit minimizing projection, evaluated at the scalar axis optimizer. -/
def minimizingProjection (C A₁ A₂ B₁ B₂ : ℝ) : Mat :=
  let j := minimizingMode C A₁ A₂ B₁ B₂
  let B := ![B₁, B₂] j
  axisProjection j (favorableContrast B (axisArg (![A₁, A₂] j) |B|))

private theorem axisArg_sq_le_one {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    axisArg A b ^ 2 ≤ 1 := by
  unfold axisArg
  split_ifs with hA₀ hba
  · norm_num
  · have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA₀)
    have h₀ : 0 ≤ b / A := div_nonneg hb hA
    have h₁ : b / A ≤ 1 := (div_le_iff₀ hpos).2 (by simpa using hba)
    nlinarith only [mul_nonneg h₀ (sub_nonneg.mpr h₁), h₁]
  · norm_num

/-- The physical minimum is attained on a single mode, with zero contrast and
zero crossing cost in the spectator mode. -/
theorem minimizingProjection_spec {C A₁ A₂ B₁ B₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    let j := minimizingMode C A₁ A₂ B₁ B₂
    let P := minimizingProjection C A₁ A₂ B₁ B₂
    P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
      occupationContrast P (1 - j) = 0 ∧ 1 - (within P (1 - j)).re = 0 ∧
      orientationValue C A₁ A₂ B₁ B₂ P = twoModeMinimum C A₁ A₂ |B₁| |B₂| := by
  let j := minimizingMode C A₁ A₂ B₁ B₂
  let B := ![B₁, B₂] j
  let u := axisArg (![A₁, A₂] j) |B|
  have hA (i : Fin 2) : 0 ≤ ![A₁, A₂] i := by
    fin_cases i
    · exact hA₁
    · exact hA₂
  have hu : u ^ 2 ≤ 1 := axisArg_sq_le_one (hA j) (abs_nonneg B)
  have hz : favorableContrast B u ^ 2 ≤ 1 := by rwa [favorableContrast_sq]
  let P := axisProjection j (favorableContrast B u)
  change P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
    occupationContrast P (1 - j) = 0 ∧ 1 - (within P (1 - j)).re = 0 ∧
    orientationValue C A₁ A₂ B₁ B₂ P = twoModeMinimum C A₁ A₂ |B₁| |B₂|
  obtain ⟨hHerm, hP, hRank, _, hother, _, hcross⟩ := axisProjection_spec j hz
  have hcross' : 2 * (1 - (within P (1 - j)).re) = 0 := hcross
  refine ⟨hHerm, hP, hRank, hother, by linarith only [hcross'], ?_⟩
  change orientationValue C A₁ A₂ B₁ B₂ (axisProjection j (favorableContrast B u)) = _
  rw [orientationValue_axisProjection C A₁ A₂ B₁ B₂ j hu]
  change axisMinimum C (![A₁, A₂] j) |B| = twoModeMinimum C A₁ A₂ |B₁| |B₂|
  by_cases hm : axisMinimum C A₁ |B₁| ≤ axisMinimum C A₂ |B₂|
  · have hj : j = 0 := ite_eq_left hm
    change axisMinimum C (![A₁, A₂] j) (abs (![B₁, B₂] j)) = _
    rw [hj]
    exact (min_eq_left hm).symm
  · have hj : j = 1 := ite_eq_right hm
    change axisMinimum C (![A₁, A₂] j) (abs (![B₁, B₂] j)) = _
    rw [hj]
    exact (min_eq_right (le_of_not_ge hm)).symm

/-- The scalar minimum is the least physical orientation value on the complex
rank-two CAR orbit. Its witness is `minimizingProjection`. -/
theorem rank_two_orientation_exact_minimum {C A₁ A₂ B₁ B₂ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    IsLeast {v : ℝ | ∃ P : Mat, P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
      orientationValue C A₁ A₂ B₁ B₂ P = v}
      (twoModeMinimum C A₁ A₂ |B₁| |B₂|) := by
  constructor
  · obtain ⟨hHerm, hP, hRank, _, _, hvalue⟩ :=
      minimizingProjection_spec (C := C) (B₁ := B₁) (B₂ := B₂) hA₁ hA₂
    exact ⟨minimizingProjection C A₁ A₂ B₁ B₂, hHerm, hP, hRank, hvalue⟩
  · rintro v ⟨P, hHerm, hP, hRank, rfl⟩
    exact rank_two_orientation_lower hA₁ hA₂ hHerm hP hRank

end D5.S3.Quantum.Semigroups.WuTwoModeRankTwoAttainedOrientation
