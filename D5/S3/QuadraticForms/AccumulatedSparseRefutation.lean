/- GID: D5/S3/QuadraticForms/AccumulatedSparseRefutation
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/AccumulatedSparseRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/AccumulatedSparseRefutation.claim; result=D5/S3/QuadraticForms/AccumulatedSparseRefutation.result; claim=D5/S3/QuadraticForms/AccumulatedSparseRefutation.claim
   digest: An equicorrelated contraction violates the accumulated sparse minimum bound. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
The two source assertions are due to Ekene E., MathOverflow 509794,
revision 2, https://mathoverflow.net/revisions/509794/2 (CC BY-SA 4.0).
All sparse coefficients are real. The infimum below is shown to be attained
for the counterexample, so it is the source's actual minimum.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix Finset

namespace D5.S3.QuadraticForms.AccumulatedSparseRefutation

def errorSet {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    (d : ℕ) : Set ℝ :=
  {r | ∃ z : Fin m → ℝ, (univ.filter fun i => z i ≠ 0).card ≤ d ∧
    r = (x - z) ⬝ᵥ (K *ᵥ (x - z))}

def tauSq {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    (d : ℕ) : ℝ := sInf (errorSet K x d)

/-- The original finite assertion, with the Euclidean contraction written as
the equivalent inequality between sums of coordinate squares. -/
def claim : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (K : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ),
    K.PosSemidef →
    (∀ y : Fin m → ℝ, (∑ i, (K *ᵥ y) i ^ 2) ≤ ∑ i, y i ^ 2) →
    (∀ i, 0 ≤ x i) → (∑ i, x i ^ 2) = 1 →
    (∀ i, K i i ≤ x i ^ 2) →
    (∑ d ∈ Icc 1 (m - 1), tauSq K x d) ≤ 1

def matrix : Matrix (Fin 64) (Fin 64) ℝ :=
  fun i j => ((if i = j then 1 else 0) + 1) / 128

def vector : Fin 64 → ℝ := fun _ => 1 / 8

def optimum (d : ℕ) : ℝ := 65 * (64 - (d : ℝ)) / (8192 * ((d : ℝ) + 1))

def total : ℝ := ∑ d ∈ Icc 1 63, optimum d

private theorem matrix_apply (y : Fin 64 → ℝ) (i : Fin 64) :
    (matrix *ᵥ y) i = (y i + ∑ j, y j) / 128 := by
  classical
  simp only [Matrix.mulVec, dotProduct, matrix]
  simp_rw [add_div, add_mul, div_mul_eq_mul_div]
  rw [sum_add_distrib, ← sum_div]
  simp [← sum_div]

theorem quadratic (y : Fin 64 → ℝ) :
    y ⬝ᵥ (matrix *ᵥ y) = ((∑ i, y i ^ 2) + (∑ i, y i) ^ 2) / 128 := by
  change (∑ i, y i * (matrix *ᵥ y) i) = _
  simp_rw [matrix_apply]
  simp_rw [show ∀ a b : ℝ, a * ((a + b) / 128) = (a ^ 2 + a * b) / 128 by
    intro a b; ring]
  rw [← sum_div, sum_add_distrib, ← sum_mul]
  ring

private theorem sparse_expansion (z : Fin 64 → ℝ) :
    (vector - z) ⬝ᵥ (matrix *ᵥ (vector - z)) =
      (65 + (∑ i, z i ^ 2) - (65 / 4) * (∑ i, z i) + (∑ i, z i) ^ 2) / 128 := by
  rw [quadratic]
  have h₁ : (∑ i, (vector - z) i) = 8 - ∑ i, z i := by
    norm_num [vector, sum_sub_distrib]
  have h₂ : (∑ i, (vector - z) i ^ 2) =
      1 - (1 / 4) * (∑ i, z i) + ∑ i, z i ^ 2 := by
    simp only [Pi.sub_apply, vector]
    simp_rw [show ∀ t : ℝ, (1 / 8 - t) ^ 2 = 1 / 64 - (1 / 4) * t + t ^ 2 by
      intro t; ring]
    simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [h₁, h₂]
  ring

private theorem sparse_cauchy (z : Fin 64 → ℝ) (d : ℕ)
    (hz : (univ.filter fun i => z i ≠ 0).card ≤ d) :
    (∑ i, z i) ^ 2 ≤ (d : ℝ) * ∑ i, z i ^ 2 := by
  classical
  let S := univ.filter fun i => z i ≠ 0
  have hs : (∑ i ∈ S, z i) = ∑ i, z i := by
    apply sum_subset (filter_subset _ _)
    intro i hi hn
    have : z i = 0 := by simpa [S] using hn
    exact this
  have hq : (∑ i ∈ S, z i ^ 2) = ∑ i, z i ^ 2 := by
    apply sum_subset (filter_subset _ _)
    intro i hi hn
    have : z i = 0 := by simpa [S] using hn
    simp [this]
  have h := sq_sum_le_card_mul_sum_sq (s := S) (f := z)
  rw [hs, hq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hz)
    (sum_nonneg fun i _ => sq_nonneg (z i)))

/-- The displayed value is the attained minimum over every real sparse vector. -/
theorem sparse_minimum (d : ℕ) (hd : 1 ≤ d) (h64 : d ≤ 64) :
    IsLeast (errorSet matrix vector d) (optimum d) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  obtain ⟨S, _, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin 64)))
    (show d ≤ univ.card by simpa using h64)
  let t : ℝ := 65 / (8 * ((d : ℝ) + 1))
  let z : Fin 64 → ℝ := fun i => if i ∈ S then t else 0
  have ht : t ≠ 0 := by dsimp [t]; positivity
  have hz : (univ.filter fun i => z i ≠ 0) = S := by
    ext i; simp [z, ht]
  have hsum : (∑ i, z i) = (d : ℝ) * t := by simp [z, hS]
  have hsumSq : (∑ i, z i ^ 2) = (d : ℝ) * t ^ 2 := by simp [z, hS]
  constructor
  · refine ⟨z, by rw [hz, hS], ?_⟩
    rw [sparse_expansion, hsum, hsumSq]
    dsimp [optimum, t]
    field_simp
    <;> ring
  · rintro r ⟨w, hw, rfl⟩
    rw [sparse_expansion]
    have hc := sparse_cauchy w d hw
    have hs := sq_nonneg (8 * ((d : ℝ) + 1) * (∑ i, w i) - 65 * d)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2
    dsimp [optimum]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 8192 * ((d : ℝ) + 1) by positivity)).2
    have hm : 0 ≤ 64 * ((d : ℝ) + 1) *
        ((d : ℝ) * (∑ i, w i ^ 2) - (∑ i, w i) ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hc)
    by_contra hf
    have hn := mul_neg_of_pos_of_neg hdR (sub_neg.mpr (lt_of_not_ge hf))
    nlinarith

theorem accumulation_gt_one : 1 < total := by
  norm_num [total, optimum, Finset.sum_Icc_succ_top]

private theorem admissible : matrix.PosSemidef ∧
    (∀ y : Fin 64 → ℝ, (∑ i, (matrix *ᵥ y) i ^ 2) ≤ ∑ i, y i ^ 2) := by
  constructor
  · apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      simp [matrix, eq_comm]
    · intro y
      simp only [star_trivial]
      rw [quadratic]
      positivity
  · intro y
    have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 64))) (f := y)
    simp only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at hc
    have hq : (∑ i, (matrix *ᵥ y) i ^ 2) =
        ((∑ i, y i ^ 2) + 66 * (∑ i, y i) ^ 2) / 16384 := by
      simp_rw [matrix_apply]
      simp_rw [show ∀ a b : ℝ, ((a + b) / 128) ^ 2 =
        (a ^ 2 + (2 * b) * a + b ^ 2) / 16384 by intro a b; ring]
      rw [← sum_div]
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [hq]
    have hA : 0 ≤ ∑ i, y i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    nlinarith

theorem result : ¬ claim := by
  intro h
  have hb := h 64 (by norm_num) matrix vector admissible.1 admissible.2
    (by intro i; norm_num [vector]) (by norm_num [vector])
    (by intro i; norm_num [matrix, vector])
  have he : (∑ d ∈ Icc 1 63, tauSq matrix vector d) = total := by
    apply sum_congr rfl
    intro d hd
    exact (sparse_minimum d (mem_Icc.mp hd).1 (le_trans (mem_Icc.mp hd).2
      (by norm_num))).csInf_eq
  norm_num at hb
  rw [he] at hb
  exact (not_le.mpr accumulation_gt_one) hb

end D5.S3.QuadraticForms.AccumulatedSparseRefutation
