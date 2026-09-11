/- GID: D5/S3/ArithSums/CenteredEuclideanEndpoint
   generality: G
   mirror-B: D5/B/S3/ArithSums/CenteredEuclideanEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The centered Euclidean lower endpoint is coordinatewise monotone with exact nonnegative ray equality. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-! # The centered Euclidean lower endpoint

For dimension at least two, subtract the centered Euclidean norm divided by
`sqrt (k * (k - 1))` from the coordinate mean. Increasing coordinates cannot
decrease this endpoint. A positive single-coordinate increment leaves it
unchanged exactly on a nonnegative coordinate ray translated by a constant.
-/

noncomputable section

open scoped BigOperators

namespace D5.S3.ArithSums.CenteredEuclideanEndpoint

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

def ones (k : ℕ) : E k := WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))

local notation:max "e" i:max => EuclideanSpace.single i (1 : ℝ)

variable {k : ℕ}

def mean (hk : 2 ≤ k) (x : E k) : ℝ := (∑ j, x j) / (k : ℝ)

def center (hk : 2 ≤ k) (x : E k) : E k := x - mean hk x • ones k

def denom (hk : 2 ≤ k) : ℝ := Real.sqrt ((k : ℝ) * ((k : ℝ) - 1))

def lower (hk : 2 ≤ k) (x : E k) : ℝ := mean hk x - ‖center hk x‖ / denom hk

variable (hk : 2 ≤ k)

private theorem dim_pos (hk : 2 ≤ k) : (0 : ℝ) < (k : ℝ) := by
  exact_mod_cast (show 0 < k by omega)

private theorem dim_sub_one_pos (hk : 2 ≤ k) : 0 < (k : ℝ) - 1 := by
  have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

private theorem denom_pos : 0 < denom hk :=
  Real.sqrt_pos.mpr (mul_pos (dim_pos hk) (dim_sub_one_pos hk))

private theorem mean_eq_expect (x : E k) :
    mean hk x = Finset.expect Finset.univ (fun j => x j) := by
  simpa only [mean, Fintype.card_fin] using
    (Fintype.expect_eq_sum_div_card (fun j : Fin k => x j)).symm

private theorem mean_add (x y : E k) :
    mean hk (x + y) = mean hk x + mean hk y := by
  simpa only [mean_eq_expect, PiLp.add_apply] using
    (Finset.expect_add_distrib Finset.univ (fun j => x j) (fun j => y j))

private theorem mean_sub (x y : E k) :
    mean hk (x - y) = mean hk x - mean hk y := by
  simpa only [mean_eq_expect, PiLp.sub_apply] using
    (Finset.expect_sub_distrib Finset.univ (fun j => x j) (fun j => y j))

private theorem mean_smul (a : ℝ) (x : E k) :
    mean hk (a • x) = a * mean hk x := by
  simpa only [mean_eq_expect, PiLp.smul_apply, smul_eq_mul] using
    (Finset.smul_expect a Finset.univ (fun j => x j)).symm

private theorem mean_constant (a : ℝ) : mean hk (a • ones k) = a := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  simpa only [mean_eq_expect, ones, PiLp.smul_apply, PiLp.toLp_apply,
    smul_eq_mul, mul_one] using Finset.expect_const hne a

private theorem mean_single (i : Fin k) : mean hk (e i) = 1 / (k : ℝ) := by
  simp [mean, EuclideanSpace.single, PiLp.single_apply]

private theorem center_apply (x : E k) (j : Fin k) :
    center hk x j = x j - (∑ l, x l) / (k : ℝ) := by
  simp [center, ones, mean]

private theorem center_add (x y : E k) :
    center hk (x + y) = center hk x + center hk y := by
  simp only [center, mean_add, add_smul]
  module

private theorem center_sub (x y : E k) :
    center hk (x - y) = center hk x - center hk y := by
  simp only [center, mean_sub, sub_smul]
  module

private theorem center_smul (a : ℝ) (x : E k) :
    center hk (a • x) = a • center hk x := by
  simp only [center, mean_smul, smul_sub, mul_smul]

private theorem center_constant (a : ℝ) : center hk (a • ones k) = 0 := by
  rw [center, mean_constant, sub_self]

private theorem center_zero : center hk (0 : E k) = 0 := by
  simpa only [zero_smul] using center_constant hk 0

theorem mean_add_single (x : E k) (i : Fin k) (u : ℝ) :
    mean hk (x + u • e i) = mean hk x + u / (k : ℝ) := by
  rw [mean_add, mean_smul, mean_single]
  ring

theorem center_add_single (x : E k) (i : Fin k) (u : ℝ) :
    center hk (x + u • e i) = center hk x + u • center hk (e i) := by
  rw [center_add, center_smul]

theorem norm_center_single_sq_expanded (i : Fin k) :
    ‖center hk (e i)‖ ^ 2 =
      (1 - 1 / (k : ℝ)) ^ 2 + ((k : ℝ) - 1) / (k : ℝ) ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  have hcoord (j : Fin k) :
      (center hk (e i) j) ^ 2 =
        (if j = i then (1 - 1 / (k : ℝ)) ^ 2 - (1 / (k : ℝ)) ^ 2 else 0)
          + (1 / (k : ℝ)) ^ 2 := by
    simp only [center, mean_single, PiLp.sub_apply, PiLp.smul_apply,
      ones, smul_eq_mul, mul_one,
      EuclideanSpace.single, PiLp.single_apply]
    split_ifs <;> ring
  simp_rw [hcoord]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem norm_center_single_sq (i : Fin k) :
    ‖center hk (e i)‖ ^ 2 = ((k : ℝ) - 1) / (k : ℝ) := by
  rw [norm_center_single_sq_expanded]
  field_simp [ne_of_gt (dim_pos hk)]
  ring

private theorem norm_center_single_eq (i : Fin k) :
    ‖center hk (e i)‖ = denom hk / (k : ℝ) := by
  have hs := norm_center_single_sq hk i
  have hd : denom hk ^ 2 = (k : ℝ) * ((k : ℝ) - 1) :=
    Real.sq_sqrt (le_of_lt (mul_pos (dim_pos hk) (dim_sub_one_pos hk)))
  have hsq : (denom hk / (k : ℝ)) ^ 2 = ((k : ℝ) - 1) / (k : ℝ) := by
    rw [div_pow, hd]
    field_simp
  have hn := norm_nonneg (center hk (e i))
  have hq := div_pos (denom_pos hk) (dim_pos hk)
  nlinarith

theorem norm_center_single_div (i : Fin k) :
    ‖center hk (e i)‖ / denom hk = 1 / (k : ℝ) := by
  rw [norm_center_single_eq]
  field_simp [ne_of_gt (denom_pos hk)]

private theorem center_single_ne_zero (i : Fin k) : center hk (e i) ≠ 0 := by
  have h := norm_center_single_eq hk i
  have hp := div_pos (denom_pos hk) (dim_pos hk)
  intro hz
  rw [hz, norm_zero] at h
  linarith

private theorem smul_center_single_ne_zero (i : Fin k) (u : ℝ) (hu : 0 < u) :
    u • center hk (e i) ≠ 0 :=
  smul_ne_zero (ne_of_gt hu) (center_single_ne_zero hk i)

theorem center_eq_zero_iff_constant (x : E k) :
    center hk x = 0 ↔ ∃ a : ℝ, x = a • ones k := by
  constructor
  · intro h
    exact ⟨mean hk x, sub_eq_zero.mp h⟩
  · rintro ⟨a, rfl⟩
    exact center_constant hk a

theorem lower_add_single_sub (x : E k) (i : Fin k) (u : ℝ) :
    lower hk (x + u • e i) - lower hk x =
      u / (k : ℝ) -
        (‖center hk x + u • center hk (e i)‖ - ‖center hk x‖) / denom hk := by
  simp only [lower, mean_add_single, center_add_single]
  ring

theorem lower_le_add_single (x : E k) (i : Fin k) (u : ℝ) (hu : 0 ≤ u) :
    lower hk x ≤ lower hk (x + u • e i) := by
  have htri := norm_add_le (center hk x) (u • center hk (e i))
  rw [norm_smul_of_nonneg hu] at htri
  have hdiv := (div_le_div_iff_of_pos_right (denom_pos hk)).mpr
    (show ‖center hk x + u • center hk (e i)‖ - ‖center hk x‖ ≤
      u * ‖center hk (e i)‖ by linarith)
  rw [mul_div_assoc, norm_center_single_div, mul_one_div] at hdiv
  have hinc := lower_add_single_sub hk x i u
  nlinarith

theorem lower_add_zero_single (x : E k) (i : Fin k) :
    lower hk (x + (0 : ℝ) • e i) = lower hk x := by
  simp

theorem lower_add_single_eq_iff_centered (x : E k) (i : Fin k) (u : ℝ) (hu : 0 < u) :
    lower hk (x + u • e i) = lower hk x ↔
      ∃ t : ℝ, 0 ≤ t ∧ center hk x = t • center hk (e i) := by
  have hd := ne_of_gt (denom_pos hk)
  have hscale : ‖u • center hk (e i)‖ / denom hk = u / (k : ℝ) := by
    rw [norm_smul_of_nonneg hu.le, mul_div_assoc, norm_center_single_div]
    ring
  have heq : lower hk (x + u • e i) = lower hk x ↔
      ‖center hk x + u • center hk (e i)‖ =
        ‖center hk x‖ + ‖u • center hk (e i)‖ := by
    have hinc := lower_add_single_sub hk x i u
    rw [← hscale] at hinc
    constructor
    · intro h
      have he : (‖center hk x + u • center hk (e i)‖ - ‖center hk x‖) /
          denom hk = ‖u • center hk (e i)‖ / denom hk := by linarith
      have := (div_left_inj' hd).mp he
      linarith
    · intro h
      rw [h, add_sub_cancel_left] at hinc
      linarith
  rw [heq, norm_add_eq_iff_real]
  have hray : (‖u • center hk (e i)‖ • center hk x =
        ‖center hk x‖ • (u • center hk (e i))) ↔
      SameRay ℝ (center hk x) (u • center hk (e i)) := by
    rw [sameRay_iff_norm_smul_eq]
    exact eq_comm
  rw [hray, ← exists_nonneg_right_iff_sameRay (smul_center_single_ne_zero hk i u hu)]
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t * u, mul_nonneg ht hu.le, by simpa only [mul_smul] using hx⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨t / u, div_nonneg ht hu.le, ?_⟩
    rw [← mul_smul, div_mul_cancel₀ _ (ne_of_gt hu)]
    exact hx

theorem centered_ray_iff_translated_single (x : E k) (i : Fin k) :
    (∃ t : ℝ, 0 ≤ t ∧ center hk x = t • center hk (e i)) ↔
      ∃ a t : ℝ, 0 ≤ t ∧ x = a • ones k + t • e i := by
  constructor
  · rintro ⟨t, ht, hx⟩
    have hz : center hk (x - t • e i) = 0 := by
      rw [center_sub, center_smul, hx, sub_self]
    obtain ⟨a, ha⟩ := (center_eq_zero_iff_constant hk (x - t • e i)).mp hz
    exact ⟨a, t, ht, sub_eq_iff_eq_add.mp ha⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ⟨t, ht, by rw [center_add, center_constant, center_smul, zero_add]⟩

theorem lower_add_single_eq_iff_translated (x : E k) (i : Fin k) (u : ℝ) (hu : 0 < u) :
    lower hk (x + u • e i) = lower hk x ↔
      ∃ a t : ℝ, 0 ≤ t ∧ x = a • ones k + t • e i :=
  (lower_add_single_eq_iff_centered hk x i u hu).trans
    (centered_ray_iff_translated_single hk x i)

theorem lower_le_of_pointwise_le (x y : E k) (hxy : ∀ j : Fin k, x j ≤ y j) :
    lower hk x ≤ lower hk y := by
  classical
  have hprogress : Monotone (fun s : Finset (Fin k) =>
      lower hk (x + ∑ j ∈ s, (y j - x j) • e j)) := by
    apply Finset.monotone_iff_forall_le_insert.mpr
    intro s i hi
    rw [Finset.sum_insert hi]
    have hstep := lower_le_add_single hk
      (x + ∑ j ∈ s, (y j - x j) • e j) i (y i - x i) (sub_nonneg.mpr (hxy i))
    have he : x + ((y i - x i) • e i + ∑ j ∈ s, (y j - x j) • e j) =
        (x + ∑ j ∈ s, (y j - x j) • e j) + (y i - x i) • e i := by abel
    rw [he]
    exact hstep
  have hreconstruct : x + ∑ j : Fin k, (y j - x j) • e j = y := by
    apply PiLp.ext
    intro i
    simp [EuclideanSpace.single, Pi.single_apply]
  simpa only [Finset.sum_empty, add_zero, hreconstruct] using
    hprogress (Finset.empty_subset (Finset.univ : Finset (Fin k)))

end D5.S3.ArithSums.CenteredEuclideanEndpoint
