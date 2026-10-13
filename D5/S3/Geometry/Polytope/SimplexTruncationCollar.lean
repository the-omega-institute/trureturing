import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic

/-! # Marked collars for truncated finite simplices

Finite-sum collar maps identify the fixed coordinate truncation with the simplex cut by
rows of a matrix with diagonal entries one and off-diagonal entries less than minus one.
The maps preserve the labeled coordinate faces, cap faces, and ordered endpoints.
-/
noncomputable section
open Set
open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.Geometry.Polytope.SimplexTruncationCollar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fixed truncation does not depend on a matrix. -/
def standard : Set (ι → ℝ) :=
  stdSimplex ℝ ι ∩ {x | ∀ i, x i ≤ 2 / 3}

def row (A : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ := ∑ j, A i j * x j

def cut (A : ι → ι → ℝ) : Set (ι → ℝ) :=
  stdSimplex ℝ ι ∩ {x | ∀ i, row A x i ≤ 0}

/-- Opposite-face coordinates, used only where the denominator is positive. -/
def direction (i : ι) (x : ι → ℝ) : ι → ℝ :=
  fun j => if j = i then 0 else x j / (1 - x i)

/-- A ray from the opposite face towards its labeled vertex. -/
def ray (i : ι) (u : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun j => if j = i then t else (1 - t) * u j

@[simp] theorem direction_at (i : ι) (x : ι → ℝ) : direction i x i = 0 := by
  simp [direction]

@[simp] theorem ray_at (i : ι) (u : ι → ℝ) (t : ℝ) : ray i u t i = t := by
  simp [ray]

theorem ray_other (i : ι) (u : ι → ℝ) (t : ℝ) {j : ι} (hji : j ≠ i) :
    ray i u t j = (1 - t) * u j := by simp [ray, hji]

theorem other_le_half {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    {i j : ι} (hi : 1 / 2 < x i) (hji : j ≠ i) : x j < 1 / 2 := by
  have h := Finset.add_le_sum (s := Finset.univ) (f := x) (fun k _ => hx.1 k)
    (Finset.mem_univ i) (Finset.mem_univ j) hji.symm
  rw [hx.2] at h
  linarith

theorem unique_large {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    {i j : ι} (hi : 1 / 2 < x i) (hj : 1 / 2 < x j) : i = j := by
  by_contra h
  have hji : j ≠ i := fun hji => h hji.symm
  exact (not_lt_of_ge (other_le_half hx hi hji).le) hj

theorem direction_mem {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    (i : ι) (hi : x i < 1) : direction i x ∈ stdSimplex ℝ ι := by
  have hd : 0 < 1 - x i := sub_pos.mpr hi
  refine ⟨fun j => ?_, ?_⟩
  · by_cases hji : j = i
    · simp [direction, hji]
    · simp only [direction, if_neg hji]
      exact div_nonneg (hx.1 j) hd.le
  · have hs : (∑ j ∈ Finset.univ.erase i, x j) = 1 - x i := by
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) x (Finset.mem_univ i)
      rw [hx.2] at h
      linarith
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [direction_at, add_zero]
    calc
      (∑ j ∈ Finset.univ.erase i, direction i x j) =
          ∑ j ∈ Finset.univ.erase i, x j / (1 - x i) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [direction, Finset.ne_of_mem_erase hj]
      _ = (∑ j ∈ Finset.univ.erase i, x j) / (1 - x i) := by
        rw [Finset.sum_div]
      _ = 1 := by rw [hs, div_self hd.ne']

theorem ray_direction {x : ι → ℝ} (i : ι) (hi : x i < 1) :
    ray i (direction i x) (x i) = x := by
  funext j
  by_cases hji : j = i
  · simp [ray, hji]
  · simp only [ray, direction, if_neg hji]
    field_simp [(sub_pos.mpr hi).ne']

theorem direction_ray (i : ι) {u : ι → ℝ} (hu : u i = 0)
    {t : ℝ} (ht : t < 1) : direction i (ray i u t) = u := by
  funext j
  by_cases hji : j = i
  · subst j; simp [hu]
  · simp only [direction, if_neg hji, ray_at, ray_other i u t hji]
    field_simp [(sub_pos.mpr ht).ne']

theorem ray_mem (i : ι) {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι)
    (hui : u i = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ray i u t ∈ stdSimplex ℝ ι := by
  have he : ray i u t = fun j => (Pi.single i t : ι → ℝ) j + (1-t)*u j := by
    funext j
    by_cases hji : j = i
    · subst j; simp [ray, hui]
    · simp [ray, hji]
  rw [he]
  refine ⟨fun j => ?_, ?_⟩
  · have h : 0 ≤ (Pi.single i t : ι → ℝ) j := by
      by_cases hji : j = i <;> simp [hji, ht0]
    exact add_nonneg h (mul_nonneg (sub_nonneg.mpr ht1) (hu.1 j))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hu.2, Pi.single_apply]
    <;> ring

theorem ray_side_zero (i : ι) {u : ι → ℝ} {s t : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (j : ι) :
    ray i u s j = 0 ↔ ray i u t j = 0 := by
  by_cases hji : j = i
  · subst j; simp [hs0.ne', ht0.ne']
  · simp only [ray_other i u s hji, ray_other i u t hji, mul_eq_zero]
    simp [(sub_pos.mpr hs1).ne', (sub_pos.mpr ht1).ne']

variable (A : ι → ι → ℝ)

/-- The strict row estimate holds on the whole simplex away from the relevant vertex. -/
theorem row_lt (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    (i : ι) (hi : x i < 1) : row A x i < 2*x i - 1 := by
  have hs : (∑ j ∈ Finset.univ.erase i, x j) + x i = 1 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), hx.2]
  have hex : ∃ j ∈ Finset.univ.erase i, 0 < x j := by
    by_contra h
    push_neg at h
    have hz : (∑ j ∈ Finset.univ.erase i, x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact le_antisymm (h j hj) (hx.1 j)
    rw [hz] at hs
    linarith
  have hlt : (∑ j ∈ Finset.univ.erase i, A i j * x j) <
      ∑ j ∈ Finset.univ.erase i, -x j := by
    apply Finset.sum_lt_sum
    · intro j hj
      simpa using mul_le_mul_of_nonneg_right
        (hoff i j (Finset.ne_of_mem_erase hj).symm).le (hx.1 j)
    · obtain ⟨j,hj,hpos⟩ := hex
      refine ⟨j, hj, ?_⟩
      simpa only [neg_one_mul] using
        (mul_lt_mul_of_pos_right (hoff i j (Finset.ne_of_mem_erase hj).symm) hpos)
  have hr : row A x i = x i + ∑ j ∈ Finset.univ.erase i, A i j * x j := by
    unfold row
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag, one_mul, add_comm]
  rw [Finset.sum_neg_distrib] at hlt
  linarith

/-- Two different retained cap planes cannot meet even on the parent simplex. -/
theorem pair_row_neg (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι)
    {i j : ι} (hij : i ≠ j) : row A x i + row A x j < 0 := by
  have hc (k : ι) : A i k + A j k < 0 := by
    by_cases hki : k = i
    · subst k; rw [hdiag]; linarith [hoff j i hij.symm]
    by_cases hkj : k = j
    · subst k; rw [hdiag]; linarith [hoff i j hij]
    linarith [hoff i k (Ne.symm hki), hoff j k (Ne.symm hkj)]
  have hp : ∃ k, 0 < x k := by
    by_contra h
    push_neg at h
    have hz : ∑ k, x k = 0 := Finset.sum_eq_zero (fun k _ => le_antisymm (h k) (hx.1 k))
    linarith [hx.2]
  have hs : (∑ k, (A i k + A j k)*x k) < ∑ _k : ι, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k _; exact mul_nonpos_of_nonpos_of_nonneg (hc k).le (hx.1 k)
    · obtain ⟨k,hk⟩ := hp
      exact ⟨k,Finset.mem_univ k,mul_neg_of_neg_of_pos (hc k) hk⟩
  simpa [row, add_mul, Finset.sum_add_distrib] using hs

theorem cut_coord_lt_one (hdiag : ∀ i, A i i = 1) {x : ι → ℝ} (hx : x ∈ cut A) (i : ι) : x i < 1 := by
  have hle := (mem_Icc_of_mem_stdSimplex hx.1 i).2
  apply lt_of_le_of_ne hle
  intro he
  have hz (j : ι) (hji : j ≠ i) : x j = 0 := by
    have h := Finset.add_le_sum (s := Finset.univ) (f := x) (fun k _ => hx.1.1 k)
      (Finset.mem_univ i) (Finset.mem_univ j) hji.symm
    rw [hx.1.2, he] at h
    exact le_antisymm (by linarith) (hx.1.1 j)
  have hr : row A x i = 1 := by
    unfold row
    rw [Finset.sum_eq_single i]
    · rw [hdiag, he, one_mul]
    · intro j _ hji; rw [hz j hji, mul_zero]
    · simp
  have h := hx.2 i
  rw [hr] at h
  norm_num at h

/-- The weighted opposite-face coefficient. Its diagonal summand is zero. -/
def coefficient (i : ι) (u : ι → ℝ) : ℝ := -row A u i

def cutoff (i : ι) (u : ι → ℝ) : ℝ :=
  coefficient A i u / (1 + coefficient A i u)

def stretch (i : ι) (u : ι → ℝ) : ℝ := 6 * (cutoff A i u - 1 / 2)

theorem coefficient_gt_one (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) : 1 < coefficient A i u := by
  have h := row_lt A hdiag hoff hu i (by rw [hui]; norm_num)
  dsimp [coefficient]
  rw [hui] at h
  linarith

theorem cutoff_bounds (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) :
    1 / 2 < cutoff A i u ∧ cutoff A i u < 1 := by
  have hc := coefficient_gt_one A hdiag hoff i hu hui
  have hd : 0 < 1 + coefficient A i u := by linarith
  constructor
  · exact (lt_div_iff₀ hd).mpr (by linarith)
  · exact (div_lt_iff₀ hd).mpr (by linarith)

theorem stretch_pos (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) : 0 < stretch A i u := by
  have h := (cutoff_bounds A hdiag hoff i hu hui).1
  dsimp [stretch]
  linarith

theorem row_ray (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι)
    (hui : u i = 0) (t : ℝ) :
    row A (ray i u t) i = (1 + coefficient A i u) * (t - cutoff A i u) := by
  have he : row A (ray i u t) i = t + (1-t) * row A u i := by
    have hv : ray i u t = fun j => (Pi.single i t : ι → ℝ) j + (1-t)*u j := by
      funext j
      by_cases hji : j = i
      · subst j; simp [ray, hui]
      · simp [ray, hji]
    rw [hv]
    simp only [row, mul_add, Finset.sum_add_distrib]
    have hsingle : (∑ j, A i j * (Pi.single i t : ι → ℝ) j) = t := by
      simp [Pi.single_apply, mul_ite, hdiag]
    rw [hsingle, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _; ring
  have hc := coefficient_gt_one A hdiag hoff i hu hui
  have hd : 1 + coefficient A i u ≠ 0 := by linarith
  rw [he]
  have hr : row A u i = -coefficient A i u := by simp [coefficient]
  rw [hr]
  unfold cutoff
  field_simp [hd]
  <;> ring

theorem ray_other_row_neg (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) {t : ℝ}
    (ht0 : 1 / 2 ≤ t) (ht1 : t < 1) {j : ι} (hji : j ≠ i) :
    row A (ray i u t) j < 0 := by
  have hx := ray_mem i hu hui (by linarith : 0 ≤ t) ht1.le
  have hj : ray i u t j ≤ 1 / 2 := by
    rw [ray_other i u t hji]
    have h := mul_le_mul_of_nonneg_left (mem_Icc_of_mem_stdSimplex hu j).2
      (sub_nonneg.mpr ht1.le)
    nlinarith
  have h := row_lt A hdiag hoff hx j (by linarith)
  linarith

theorem ray_cut_iff (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) {t : ℝ}
    (ht0 : 1 / 2 ≤ t) (ht1 : t < 1) :
    ray i u t ∈ cut A ↔ t ≤ cutoff A i u := by
  have hc := coefficient_gt_one A hdiag hoff i hu hui
  have hd : 0 < 1 + coefficient A i u := by linarith
  constructor
  · intro hx
    have h := hx.2 i
    rw [row_ray A hdiag hoff i hu hui] at h
    by_contra ht
    have hp := mul_pos hd (sub_pos.mpr (lt_of_not_ge ht))
    linarith
  · intro ht
    refine ⟨ray_mem i hu hui (by linarith) ht1.le, fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      rw [row_ray A hdiag hoff i hu hui]
      exact mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.mpr ht)
    · exact (ray_other_row_neg A hdiag hoff i hu hui ht0 ht1 hji).le

/-- A single finite sum implements every collar and all their seams. -/
def deform (s : ι → (ι → ℝ) → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun k => x k + ∑ i, (s i (direction i x) - 1) * max 0 (x i - 1 / 2) *
    ((if k = i then 1 else 0) - direction i x k)

def H (x : ι → ℝ) : ι → ℝ := deform (stretch A) x

def J (x : ι → ℝ) : ι → ℝ := deform (fun i u => 1 / stretch A i u) x

theorem deform_central (s : ι → (ι → ℝ) → ℝ) {x : ι → ℝ}
    (hx : ∀ i, x i ≤ 1 / 2) : deform s x = x := by
  funext k
  have hm (i : ι) : max (0 : ℝ) (x i - 1 / 2) = 0 :=
    max_eq_left (by linarith [hx i])
  simp only [deform, hm, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

/-- On the collar at i, deformation changes only the ray parameter. -/
theorem deform_collar (s : ι → (ι → ℝ) → ℝ) {x : ι → ℝ}
    (hx : x ∈ stdSimplex ℝ ι) (i : ι) (hi : 1 / 2 < x i) (hi1 : x i < 1) :
    deform s x = ray i (direction i x) (1 / 2 + s i (direction i x)*(x i-1 / 2)) := by
  funext k
  have hsum : (∑ j, (s j (direction j x)-1)*max 0 (x j-1 / 2)*
      ((if k = j then 1 else 0)-direction j x k)) =
      (s i (direction i x)-1)*(x i-1 / 2)*
        ((if k = i then 1 else 0)-direction i x k) := by
    rw [Finset.sum_eq_single i]
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ x i-1 / 2)]
    · intro j _ hji
      have hj : x j ≤ 1 / 2 := le_of_not_gt (fun hj => hji (unique_large hx hj hi))
      rw [max_eq_left (by linarith)]
      ring
    · simp
  change x k + _ = _
  rw [hsum]
  by_cases hki : k = i
  · subst k
    rw [if_pos (rfl : i = i), direction_at, ray_at]
    ring
  · rw [ray_other i _ _ hki, if_neg hki]
    have he : x k = (1-x i)*direction i x k := by
      have := congrFun (ray_direction i hi1) k
      simpa only [ray_other i _ _ hki] using this.symm
    rw [he]
    ring

theorem H_central {x : ι → ℝ} (hx : ∀ i, x i ≤ 1 / 2) : H A x = x :=
  deform_central (stretch A) hx

theorem J_central {x : ι → ℝ} (hx : ∀ i, x i ≤ 1 / 2) : J A x = x :=
  deform_central (fun i u => 1/stretch A i u) hx

theorem standard_lt_one {x : ι → ℝ} (hx : x ∈ (standard : Set (ι → ℝ)))
    (i : ι) : x i < 1 := by linarith [hx.2 i]

/-- Forward collar parameter and its bounds, including the terminal cap. -/
theorem forward_bounds (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) {t : ℝ}
    (ht0 : 1 / 2 < t) (ht1 : t ≤ 2 / 3) :
    1 / 2 < 1 / 2 + stretch A i u*(t-1 / 2) ∧
    1 / 2 + stretch A i u*(t-1 / 2) ≤ cutoff A i u := by
  have hs := stretch_pos A hdiag hoff i hu hui
  constructor
  · have := mul_pos hs (sub_pos.mpr ht0)
    linarith
  · have h := mul_le_mul_of_nonneg_left (show t-1 / 2 ≤ 1 / 6 by linarith) hs.le
    dsimp [stretch] at h ⊢
    linarith

theorem backward_bounds (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (i : ι) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) (hui : u i = 0) {t : ℝ}
    (ht0 : 1 / 2 < t) (ht1 : t ≤ cutoff A i u) :
    1 / 2 < 1 / 2 + (1/stretch A i u)*(t-1 / 2) ∧
    1 / 2 + (1/stretch A i u)*(t-1 / 2) ≤ 2 / 3 := by
  have hs := stretch_pos A hdiag hoff i hu hui
  have he : (1/stretch A i u)*(t-1 / 2) = (t-1 / 2)/stretch A i u := by ring
  rw [he]
  constructor
  · have := div_pos (sub_pos.mpr ht0) hs
    linarith
  · have h : (t-1 / 2)/stretch A i u ≤ 1 / 6 := by
      apply (div_le_iff₀ hs).mpr
      dsimp [stretch]
      linarith
    linarith

theorem H_mem (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ (standard : Set (ι → ℝ))) : H A x ∈ cut A := by
  by_cases hc : ∀ i, x i ≤ 1 / 2
  · rw [H_central A hc]
    refine ⟨hx.1, fun i => ?_⟩
    have h := row_lt A hdiag hoff hx.1 i (standard_lt_one hx i)
    linarith [hc i]
  · push_neg at hc
    obtain ⟨i,hi⟩ := hc
    have hu := direction_mem hx.1 i (standard_lt_one hx i)
    have ht := forward_bounds A hdiag hoff i hu (direction_at i x) hi (hx.2 i)
    have hb := cutoff_bounds A hdiag hoff i hu (direction_at i x)
    rw [H, deform_collar (stretch A) hx.1 i hi (standard_lt_one hx i)]
    exact (ray_cut_iff A hdiag hoff i hu (direction_at i x) ht.1.le
      (ht.2.trans_lt hb.2)).mpr ht.2

theorem J_mem (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ cut A) : J A x ∈ (standard : Set (ι → ℝ)) := by
  by_cases hc : ∀ i, x i ≤ 1 / 2
  · rw [J_central A hc]
    exact ⟨hx.1, fun i => by linarith [hc i]⟩
  · push_neg at hc
    obtain ⟨i,hi⟩ := hc
    have hi1 := cut_coord_lt_one A hdiag hx i
    have hu := direction_mem hx.1 i hi1
    have hcut : x i ≤ cutoff A i (direction i x) :=
      (ray_cut_iff A hdiag hoff i hu (direction_at i x) hi.le hi1).mp
        (by rw [ray_direction i hi1]; exact hx)
    have ht := backward_bounds A hdiag hoff i hu (direction_at i x) hi hcut
    rw [J, deform_collar (fun i u => 1/stretch A i u) hx.1 i hi hi1]
    have hy := ray_mem i hu (direction_at i x) (by linarith :
      0 ≤ 1 / 2 + (1/stretch A i (direction i x))*(x i-1 / 2))
      (by linarith : 1 / 2 + (1/stretch A i (direction i x))*(x i-1 / 2) ≤ 1)
    refine ⟨hy, fun j => ?_⟩
    by_cases hji : j = i
    · subst j; simpa only [ray_at] using ht.2
    · have h := other_le_half hy (i := i) (by simpa only [ray_at] using ht.1) hji
      linarith

theorem J_H (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ (standard : Set (ι → ℝ))) : J A (H A x) = x := by
  by_cases hc : ∀ i, x i ≤ 1 / 2
  · rw [H_central A hc, J_central A hc]
  · push_neg at hc
    obtain ⟨i,hi⟩ := hc
    have hi1 := standard_lt_one hx i
    have hu := direction_mem hx.1 i hi1
    have hs := stretch_pos A hdiag hoff i hu (direction_at i x)
    have ht := forward_bounds A hdiag hoff i hu (direction_at i x) hi (hx.2 i)
    have hb := cutoff_bounds A hdiag hoff i hu (direction_at i x)
    have he : H A x = ray i (direction i x) (1 / 2+stretch A i (direction i x)*(x i-1 / 2)) :=
      deform_collar (stretch A) hx.1 i hi hi1
    have hy := H_mem A hdiag hoff hx
    have hiy : 1 / 2 < H A x i := by rw [he, ray_at]; exact ht.1
    have hiy1 := cut_coord_lt_one A hdiag hy i
    have hdir : direction i (H A x) = direction i x := by
      rw [he]; exact direction_ray i (direction_at i x) (ht.2.trans_lt hb.2)
    rw [J, deform_collar (fun i u => 1/stretch A i u) hy.1 i hiy hiy1, hdir, he, ray_at]
    have htinv : 1 / 2 + (1/stretch A i (direction i x))*
        (1 / 2+stretch A i (direction i x)*(x i-1 / 2)-1 / 2) = x i := by
      field_simp [hs.ne']
      <;> ring
    rw [htinv, ray_direction i hi1]

theorem H_J (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ cut A) : H A (J A x) = x := by
  by_cases hc : ∀ i, x i ≤ 1 / 2
  · rw [J_central A hc, H_central A hc]
  · push_neg at hc
    obtain ⟨i,hi⟩ := hc
    have hi1 := cut_coord_lt_one A hdiag hx i
    have hu := direction_mem hx.1 i hi1
    have hs := stretch_pos A hdiag hoff i hu (direction_at i x)
    have hcut : x i ≤ cutoff A i (direction i x) :=
      (ray_cut_iff A hdiag hoff i hu (direction_at i x) hi.le hi1).mp
        (by rw [ray_direction i hi1]; exact hx)
    have ht := backward_bounds A hdiag hoff i hu (direction_at i x) hi hcut
    have he : J A x = ray i (direction i x) (1 / 2+(1/stretch A i (direction i x))*(x i-1 / 2)) :=
      deform_collar (fun i u => 1/stretch A i u) hx.1 i hi hi1
    have hy := J_mem A hdiag hoff hx
    have hiy : 1 / 2 < J A x i := by rw [he, ray_at]; exact ht.1
    have hiy1 := standard_lt_one hy i
    have hdir : direction i (J A x) = direction i x := by
      rw [he]; exact direction_ray i (direction_at i x) (by linarith)
    rw [H, deform_collar (stretch A) hy.1 i hiy hiy1, hdir, he, ray_at]
    have htinv : 1 / 2+stretch A i (direction i x)*
        (1 / 2+(1/stretch A i (direction i x))*(x i-1 / 2)-1 / 2) = x i := by
      field_simp [hs.ne']
      <;> ring
    rw [htinv, ray_direction i hi1]

theorem continuous_direction (s : Set (ι → ℝ))
    (hlt : ∀ x ∈ s, ∀ i, x i < 1) (i : ι) :
    Continuous (fun x : s => direction i x.val) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [direction_at] using (continuous_const : Continuous (fun _ : s => (0 : ℝ)))
  · simp only [direction, if_neg hji]
    exact ((continuous_apply j).comp continuous_subtype_val).div
      (continuous_const.sub ((continuous_apply i).comp continuous_subtype_val))
      (fun x => (sub_pos.mpr (hlt x.val x.property i)).ne')

theorem continuous_coefficient (i : ι) : Continuous (coefficient A i) := by
  unfold coefficient row
  fun_prop

theorem continuous_stretch (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) (s : Set (ι → ℝ)) (hs : s ⊆ stdSimplex ℝ ι)
    (hlt : ∀ x ∈ s, ∀ i, x i < 1) (i : ι) :
    Continuous (fun x : s => stretch A i (direction i x.val)) := by
  have hc := (continuous_coefficient A i).comp (continuous_direction s hlt i)
  have hd : ∀ x : s, 1 + coefficient A i (direction i x.val) ≠ 0 := by
    intro x
    have h := coefficient_gt_one A hdiag hoff i
      (direction_mem (hs x.property) i (hlt x.val x.property i)) (direction_at i x.val)
    linarith
  have ht := hc.div (continuous_const.add hc) hd
  exact continuous_const.mul (ht.sub continuous_const)

theorem continuous_deform (s : Set (ι → ℝ))
    (hlt : ∀ x ∈ s, ∀ i, x i < 1) (a : ι → (ι → ℝ) → ℝ)
    (ha : ∀ i, Continuous (fun x : s => a i (direction i x.val))) :
    Continuous (fun x : s => deform a x.val) := by
  apply continuous_pi
  intro k
  unfold deform
  apply Continuous.add ((continuous_apply k).comp continuous_subtype_val)
  apply continuous_finsetSum
  intro i _
  have hd := (continuous_apply k).comp (continuous_direction s hlt i)
  exact (((ha i).sub continuous_const).mul
    (continuous_const.max (((continuous_apply i).comp continuous_subtype_val).sub continuous_const))).mul
      (continuous_const.sub hd)

theorem continuous_H (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) : Continuous (fun x : (standard : Set (ι → ℝ)) => H A x.val) := by
  exact continuous_deform standard (fun x hx i => standard_lt_one hx i) (stretch A)
    (continuous_stretch A hdiag hoff standard (fun _ hx => hx.1)
      (fun x hx i => standard_lt_one hx i))

theorem continuous_J (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) : Continuous (fun x : cut A => J A x.val) := by
  apply continuous_deform (cut A) (fun x hx i => cut_coord_lt_one A hdiag hx i)
    (fun i u => 1/stretch A i u)
  intro i
  apply continuous_const.div
    (continuous_stretch A hdiag hoff (cut A) (fun _ hx => hx.1)
      (fun x hx i => cut_coord_lt_one A hdiag hx i) i)
  intro x
  exact (stretch_pos A hdiag hoff i
    (direction_mem x.property.1 i (cut_coord_lt_one A hdiag x.property i))
    (direction_at i x.val)).ne'

/-- The finite-sum collar homeomorphism with inverse J. -/
def homeomorph (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) : (standard : Set (ι → ℝ)) ≃ₜ cut A where
  toFun x := ⟨H A x.val, H_mem A hdiag hoff x.property⟩
  invFun x := ⟨J A x.val, J_mem A hdiag hoff x.property⟩
  left_inv x := Subtype.ext (J_H A hdiag hoff x.property)
  right_inv x := Subtype.ext (H_J A hdiag hoff x.property)
  continuous_toFun := (continuous_H A hdiag hoff).subtype_mk _
  continuous_invFun := (continuous_J A hdiag hoff).subtype_mk _

/-- The forward map preserves every labeled coordinate-zero face. -/
theorem H_side_zero (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ (standard : Set (ι → ℝ))) (j : ι) :
    H A x j = 0 ↔ x j = 0 := by
  by_cases hc : ∀ i, x i ≤ 1 / 2
  · rw [H_central A hc]
  · push_neg at hc
    obtain ⟨i,hi⟩ := hc
    have hi1 := standard_lt_one hx i
    have hu := direction_mem hx.1 i hi1
    have ht := forward_bounds A hdiag hoff i hu (direction_at i x) hi (hx.2 i)
    have hb := cutoff_bounds A hdiag hoff i hu (direction_at i x)
    have he : H A x = ray i (direction i x) (1 / 2+stretch A i (direction i x)*(x i-1 / 2)) :=
      deform_collar (stretch A) hx.1 i hi hi1
    rw [he]
    exact (ray_side_zero i (u := direction i x)
      (s := 1 / 2+stretch A i (direction i x)*(x i-1 / 2)) (t := x i)
      (by linarith) (ht.2.trans_lt hb.2) (by linarith) hi1 j).trans
      (by rw [ray_direction i hi1])

/-- The cap mark is exactly the original row-zero equation. -/
theorem H_cap_zero (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) {x : ι → ℝ} (hx : x ∈ (standard : Set (ι → ℝ))) (j : ι) :
    row A (H A x) j = 0 ↔ x j = 2 / 3 := by
  by_cases hc : ∀ i, x i ≤ 1 / 2
  · rw [H_central A hc]
    have hr := row_lt A hdiag hoff hx.1 j (standard_lt_one hx j)
    have hj := hc j
    constructor <;> intro h <;> linarith
  · push_neg at hc
    obtain ⟨i,hi⟩ := hc
    have hi1 := standard_lt_one hx i
    have hu := direction_mem hx.1 i hi1
    have ht := forward_bounds A hdiag hoff i hu (direction_at i x) hi (hx.2 i)
    have hb := cutoff_bounds A hdiag hoff i hu (direction_at i x)
    have he : H A x = ray i (direction i x) (1 / 2+stretch A i (direction i x)*(x i-1 / 2)) :=
      deform_collar (stretch A) hx.1 i hi hi1
    by_cases hji : j = i
    · subst j
      rw [he, row_ray A hdiag hoff i hu (direction_at i x)]
      have hp := coefficient_gt_one A hdiag hoff i hu (direction_at i x)
      have hd : 1+coefficient A i (direction i x) ≠ 0 := by linarith
      rw [mul_eq_zero, or_iff_right hd, sub_eq_zero]
      have hs := stretch_pos A hdiag hoff i hu (direction_at i x)
      have hsdef : stretch A i (direction i x) = 6*(cutoff A i (direction i x)-1 / 2) := rfl
      constructor
      · intro h
        have hm : stretch A i (direction i x)*(x i-2 / 3) = 0 := by nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hs.ne')
      · intro h
        rw [h, hsdef]
        ring
    · rw [he]
      have hr := ray_other_row_neg A hdiag hoff i hu (direction_at i x)
        ht.1.le (ht.2.trans_lt hb.2) hji
      have hj := other_le_half hx.1 hi hji
      constructor <;> intro h <;> linarith

/-- The source endpoint near i towards j, independently of A. -/
def standardEndpoint (i j : ι) : ι → ℝ := Pi.single i (2 / 3) + Pi.single j (1 / 3)

/-- The cutoff endpoint near i towards j. -/
def endpoint (i j : ι) : ι → ℝ :=
  Pi.single i (-A i j / (1-A i j)) + Pi.single j (1/(1-A i j))

theorem standardEndpoint_eq_ray {i j : ι} (hij : i ≠ j) :
    standardEndpoint i j = ray i (Pi.single j 1) (2 / 3) := by
  funext k
  by_cases hki : k = i
  · subst k; simp [standardEndpoint, ray, hij]
  · by_cases hkj : k = j
    · subst k; norm_num [standardEndpoint, ray, hki]
    · simp [standardEndpoint, ray, hki, hkj]

theorem standardEndpoint_mem {i j : ι} (hij : i ≠ j) :
    standardEndpoint i j ∈ (standard : Set (ι → ℝ)) := by
  rw [standardEndpoint_eq_ray hij]
  have hu : (Pi.single j (1 : ℝ) : ι → ℝ) ∈ stdSimplex ℝ ι := single_mem_stdSimplex ℝ j
  have hui : (Pi.single j (1 : ℝ) : ι → ℝ) i = 0 := by simp [hij]
  have hx := ray_mem i hu hui (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) ≤ 1)
  refine ⟨hx, fun k => ?_⟩
  by_cases hki : k = i
  · subst k; simp
  · have h := other_le_half hx (i := i) (by norm_num : (1 / 2 : ℝ) < ray i (Pi.single j 1) (2 / 3) i) hki
    linarith

theorem H_endpoint (hoff : ∀ i j, i ≠ j → A i j < -1) {i j : ι} (hij : i ≠ j) : H A (standardEndpoint i j) = endpoint A i j := by
  have hx := standardEndpoint_mem hij
  have hi : 1 / 2 < standardEndpoint i j i := by
    simp [standardEndpoint, hij]
    <;> norm_num
  have hui : (Pi.single j (1 : ℝ) : ι → ℝ) i = 0 := by simp [hij]
  have hu : direction i (standardEndpoint i j) = Pi.single j 1 := by
    rw [standardEndpoint_eq_ray hij]
    exact direction_ray i hui (by norm_num)
  have hcoord : standardEndpoint i j i = 2 / 3 := by simp [standardEndpoint, hij]
  rw [H, deform_collar (stretch A) hx.1 i hi (standard_lt_one hx i), hu, hcoord]
  have ht : 1 / 2 + stretch A i (Pi.single j 1)*(2 / 3-1 / 2) = cutoff A i (Pi.single j 1) := by
    unfold stretch; ring
  rw [ht]
  have hc : coefficient A i (Pi.single j 1) = -A i j := by
    simp [coefficient, row, Pi.single_apply, mul_ite]
  have htau : cutoff A i (Pi.single j 1) = -A i j / (1-A i j) := by
    simp [cutoff, hc, sub_eq_add_neg]
  have hd : 1-A i j ≠ 0 := by linarith [hoff i j hij]
  rw [htau]
  funext k
  by_cases hki : k = i
  · subst k; simp [ray, endpoint, hij]
  · by_cases hkj : k = j
    · subst k
      simp [ray, endpoint, hki]
      <;> field_simp [hd]
      <;> ring
    · simp [ray, endpoint, hki, hkj]

/-- All marking clauses refer to the same constructed homeomorphism. -/
theorem marked_spec (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → A i j < -1) :
    (∀ x : (standard : Set (ι → ℝ)), ∀ i,
      (homeomorph A hdiag hoff x).val i = 0 ↔ x.val i = 0) ∧
    (∀ x : (standard : Set (ι → ℝ)), ∀ i,
      row A (homeomorph A hdiag hoff x).val i = 0 ↔ x.val i = 2 / 3) ∧
    (∀ i j (hij : i ≠ j),
      (homeomorph A hdiag hoff ⟨standardEndpoint i j, standardEndpoint_mem hij⟩).val =
        endpoint A i j) ∧
    (∀ x ∈ stdSimplex ℝ ι, ∀ i j,
      0 ≤ row A x i → 0 ≤ row A x j → i = j) := by
  refine ⟨fun x i => H_side_zero A hdiag hoff x.property i,
    fun x i => H_cap_zero A hdiag hoff x.property i,
    (fun i j hij => H_endpoint A hoff hij), ?_⟩
  intro x hx i j hi hj
  by_contra hij
  have h := pair_row_neg A hdiag hoff hx hij
  linarith

end D5.S3.Geometry.Polytope.SimplexTruncationCollar
