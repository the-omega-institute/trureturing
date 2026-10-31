/- GID: D5/S3/Weil/PrimeKernel/OrderedAffineDistance
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeKernel/OrderedAffineDistance
   mirror-E: none(waiver:linked-source-local-energy)
   anchors: [Mathlib/LinearAlgebra/Matrix/PosDef]
   utility: none
   digest: Ordered affine distance kernels have an exact finite complex cut-energy decomposition. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder Matrix

namespace D5.S3.Weil.PrimeKernel.OrderedAffineDistance

def kernel {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => ((L - |t i - t j| : ℝ) : ℂ)

def realExtension {n : ℕ} (t : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n + 1 then t ⟨k, hk⟩ else 0

def complexExtension {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) : ℂ :=
  if hk : k < n + 1 then c ⟨k, hk⟩ else 0

def total {n : ℕ} (c : Fin (n + 1) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), complexExtension c j

def gapExtension {n : ℕ} (t : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  realExtension t (k + 1) - realExtension t k

def cutPrefix {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), complexExtension c j

def cutSuffix {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), if k < j then complexExtension c j else 0

def sameIndicator {n : ℕ} (i j : Fin (n + 1)) (k : ℕ) : ℝ :=
  (if i.val ≤ k ∧ j.val ≤ k then 1 else 0) +
    (if k < i.val ∧ k < j.val then 1 else 0)

def crossingIndicator {n : ℕ} (i j : Fin (n + 1)) (k : ℕ) : ℝ :=
  if i.val ≤ k ∧ k < j.val then 1
  else if j.val ≤ k ∧ k < i.val then 1 else 0

def sameIndicatorNat (i j k : ℕ) : ℝ :=
  (if i ≤ k ∧ j ≤ k then 1 else 0) +
    (if k < i ∧ k < j then 1 else 0)

theorem cut_split {n : ℕ} (c : Fin (n + 1) → ℂ) {k : ℕ} (hk : k < n) :
    total c - cutPrefix c k = cutSuffix c k := by
  unfold total cutPrefix cutSuffix
  have hprefix : (Finset.range (k + 1)).filter (fun j => j < k + 1) =
      Finset.range (k + 1) := by
    ext j
    simp
  have hleft : (Finset.range (n + 1)).filter (fun j => j ≤ k) =
      Finset.range (k + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
    (fun j => j ≤ k) (fun j => complexExtension c j)
  rw [← hsum, hleft]
  simp only [Finset.sum_filter]
  simp only [not_le]
  ring

theorem normSq_cutPrefix_expansion {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) :
    (Complex.normSq (cutPrefix c k) : ℂ) =
      ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1),
          star (complexExtension c i) * complexExtension c j := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [cutPrefix, map_sum, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [Finset.sum_comm]

theorem normSq_cutSuffix_expansion {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) :
    (Complex.normSq (cutSuffix c k) : ℂ) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          (if k < i ∧ k < j then
              star (complexExtension c i) * complexExtension c j else 0) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [cutSuffix, map_sum, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hi' : k < i <;> by_cases hj' : k < j <;> simp [hi', hj', and_comm]

theorem normSq_total_expansion {n : ℕ} (c : Fin (n + 1) → ℂ) :
    (Complex.normSq (total c) : ℂ) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          star (complexExtension c i) * complexExtension c j := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [total, map_sum, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [Finset.sum_comm]

theorem normSq_cutPrefix_indicator_expansion {n : ℕ}
    (c : Fin (n + 1) → ℂ) {k : ℕ} (hk : k < n) :
    (Complex.normSq (cutPrefix c k) : ℂ) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          (if i ≤ k ∧ j ≤ k then
              star (complexExtension c i) * complexExtension c j else 0) := by
  have hleft : (Finset.range (n + 1)).filter (fun j => j ≤ k) =
      Finset.range (k + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [normSq_cutPrefix_expansion]
  symm
  let f : ℕ → ℕ → ℂ := fun i j =>
    star (complexExtension c i) * complexExtension c j
  change (∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n + 1), if i ≤ k ∧ j ≤ k then f i j else 0) = _
  calc
    (∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1), if i ≤ k ∧ j ≤ k then f i j else 0) =
        ∑ i ∈ Finset.range (n + 1),
          if i ≤ k then
            ∑ j ∈ Finset.range (n + 1), if j ≤ k then f i j else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ≤ k <;>
        simp [h]
        <;> apply Finset.sum_congr rfl
        <;> intro j hj
        <;> by_cases h' : j ≤ k <;> simp [h, h']
    _ = ∑ i ∈ Finset.range (n + 1),
          if i ≤ k then
            ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j ≤ k), f i j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ≤ k <;> simp [h]
      rw [Finset.sum_filter]
    _ = ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i ≤ k),
          ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j ≤ k), f i j := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k + 1), f i j := by rw [hleft]

theorem same_pair_expansion {n : ℕ} (c : Fin (n + 1) → ℂ) {k : ℕ}
    (hk : k < n) :
    ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          star (complexExtension c i) * complexExtension c j *
            (sameIndicatorNat i j k : ℂ) =
      (Complex.normSq (cutPrefix c k) : ℂ) +
        (Complex.normSq (cutSuffix c k) : ℂ) := by
  rw [normSq_cutPrefix_indicator_expansion c hk, normSq_cutSuffix_expansion]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h₁ : i ≤ k ∧ j ≤ k <;>
    by_cases h₂ : k < i ∧ k < j <;>
      simp [sameIndicatorNat, h₁, h₂, Complex.ofReal_add, mul_add]

theorem realExtension_of_lt {n : ℕ} (t : Fin (n + 1) → ℝ) {k : ℕ}
    (hk : k < n + 1) : realExtension t k = t ⟨k, hk⟩ := by
  simp [realExtension, hk]

theorem abs_sub_of_le {n : ℕ} {t : Fin (n + 1) → ℝ}
    (h : Monotone t) {i j : Fin (n + 1)} (hij : i ≤ j) :
    |t i - t j| = t j - t i := by
  rw [abs_of_nonpos (sub_nonpos.mpr (h hij))]
  ring

theorem gap_sum {n : ℕ} (t : Fin (n + 1) → ℝ) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ n) :
    ∑ k ∈ Finset.Ico a b, gapExtension t k =
      t ⟨b, by omega⟩ - t ⟨a, by omega⟩ := by
  calc
    ∑ k ∈ Finset.Ico a b, gapExtension t k =
        ∑ k ∈ Finset.Ico a b,
          (realExtension t (k + 1) - realExtension t k) := by rfl
    _ = (∑ k ∈ Finset.range b,
          (realExtension t (k + 1) - realExtension t k)) -
        ∑ k ∈ Finset.range a,
          (realExtension t (k + 1) - realExtension t k) :=
      Finset.sum_Ico_eq_sub _ hab
    _ = (realExtension t b - realExtension t 0) -
        (realExtension t a - realExtension t 0) := by
      rw [Finset.sum_range_sub, Finset.sum_range_sub]
    _ = realExtension t b - realExtension t a := by ring
    _ = t ⟨b, by omega⟩ - t ⟨a, by omega⟩ := by
      rw [realExtension_of_lt t (by omega), realExtension_of_lt t (by omega)]

theorem crossing_gap_sum {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) {i j : Fin (n + 1)} (hij : i ≤ j) :
    ∑ k ∈ Finset.range n,
        (if i.val ≤ k ∧ k < j.val then gapExtension t k else 0) =
      |t i - t j| := by
  have hijval : i.val ≤ j.val := hij
  have hjn : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  have hfilter : (Finset.range n).filter (fun k => i.val ≤ k ∧ k < j.val) =
      Finset.Ico i.val j.val := by
    ext k
    simp [Finset.mem_Ico, and_assoc, and_left_comm, and_comm]
    omega
  calc
    ∑ k ∈ Finset.range n,
        (if i.val ≤ k ∧ k < j.val then gapExtension t k else 0) =
        ∑ k ∈ (Finset.range n).filter (fun k => i.val ≤ k ∧ k < j.val),
          gapExtension t k := by
            rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.Ico i.val j.val, gapExtension t k := by rw [hfilter]
    _ = t j - t i := by
      rw [gap_sum t hijval hjn]
    _ = |t i - t j| := (abs_sub_of_le hmono hij).symm

theorem total_gap_sum {n : ℕ} (t : Fin (n + 1) → ℝ) :
    ∑ k ∈ Finset.range n, gapExtension t k =
      t (Fin.last n) - t (0 : Fin (n + 1)) := by
  change (∑ k ∈ Finset.range n,
      (realExtension t (k + 1) - realExtension t k)) = _
  rw [Finset.sum_range_sub]
  rw [realExtension_of_lt t (by omega), realExtension_of_lt t (by omega)]
  congr 1 <;> rfl

theorem same_cross_partition {n : ℕ} (i j : Fin (n + 1)) (k : ℕ) :
    sameIndicator i j k + crossingIndicator i j k = 1 := by
  by_cases hik : i.val ≤ k <;> by_cases hjk : j.val ≤ k <;>
    by_cases hki : k < i.val <;> by_cases hkj : k < j.val <;>
      simp [sameIndicator, crossingIndicator, hik, hjk, hki, hkj] <;> omega

theorem crossing_gap_sum_general {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) (i j : Fin (n + 1)) :
    ∑ k ∈ Finset.range n,
        gapExtension t k * crossingIndicator i j k = |t i - t j| := by
  by_cases hij : i ≤ j
  · rw [show (fun k => gapExtension t k * crossingIndicator i j k) =
        (fun k => if i.val ≤ k ∧ k < j.val then gapExtension t k else 0) by
          funext k
          have hB : ¬ (j.val ≤ k ∧ k < i.val) := by omega
          by_cases hA : i.val ≤ k ∧ k < j.val <;>
            simp [crossingIndicator, hA, hB] <;> ring]
    simpa using crossing_gap_sum t hmono hij
  · have hji : j ≤ i := le_of_not_ge hij
    rw [show (fun k => gapExtension t k * crossingIndicator i j k) =
        (fun k => if j.val ≤ k ∧ k < i.val then gapExtension t k else 0) by
          funext k
          have hB : ¬ (i.val ≤ k ∧ k < j.val) := by omega
          by_cases hA : j.val ≤ k ∧ k < i.val <;>
            simp [crossingIndicator, hA, hB] <;> ring]
    simpa [abs_sub_comm] using crossing_gap_sum t hmono hji

theorem same_gap_sum {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) (i j : Fin (n + 1)) :
    ∑ k ∈ Finset.range n,
        gapExtension t k * sameIndicator i j k =
      (t (Fin.last n) - t (0 : Fin (n + 1))) - |t i - t j| := by
  have hpart := crossing_gap_sum_general t hmono i j
  calc
    ∑ k ∈ Finset.range n, gapExtension t k * sameIndicator i j k =
        ∑ k ∈ Finset.range n,
          (gapExtension t k - gapExtension t k * crossingIndicator i j k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hs : sameIndicator i j k =
                1 - crossingIndicator i j k := by
              linarith [same_cross_partition i j k]
            rw [hs]
            ring
    _ = (∑ k ∈ Finset.range n, gapExtension t k) -
        ∑ k ∈ Finset.range n,
          gapExtension t k * crossingIndicator i j k := by
            rw [Finset.sum_sub_distrib]
    _ = (t (Fin.last n) - t (0 : Fin (n + 1))) - |t i - t j| := by
      rw [total_gap_sum t, hpart]

theorem same_gap_sum_nat {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) {i j : ℕ} (hi : i < n + 1) (hj : j < n + 1) :
    ∑ k ∈ Finset.range n,
        gapExtension t k * sameIndicatorNat i j k =
      (t (Fin.last n) - t (0 : Fin (n + 1))) -
        |t ⟨i, hi⟩ - t ⟨j, hj⟩| := by
  simpa [sameIndicator, sameIndicatorNat] using
    (same_gap_sum t hmono ⟨i, hi⟩ ⟨j, hj⟩)


theorem kernel_hermitian {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ) :
    (kernel L t).IsHermitian := by
  ext i j
  simp [Matrix.IsHermitian, kernel, abs_sub_comm]

theorem quadratic_pair_expansion {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → ℂ) :
    star c ⬝ᵥ (kernel L t *ᵥ c) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        star (c i) * c j * (((L - |t i - t j| : ℝ) : ℂ)) := by
  simp only [dotProduct, Matrix.mulVec, kernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.star_apply, mul_assoc, mul_comm, mul_left_comm]

theorem quadratic_range_expansion {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → ℂ) :
    star c ⬝ᵥ (kernel L t *ᵥ c) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        star (complexExtension c i) * complexExtension c j *
          (((L - |realExtension t i - realExtension t j| : ℝ) : ℂ)) := by
  rw [quadratic_pair_expansion]
  simp_rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  simp only [dif_pos hi']
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < n + 1 := Finset.mem_range.mp hj
  simp only [dif_pos hj']
  simp [complexExtension, realExtension, hi', hj']

theorem pair_distance_decomposition {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) (c : Fin (n + 1) → ℂ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        star (complexExtension c i) * complexExtension c j *
          (((|realExtension t i - realExtension t j| : ℝ)) : ℂ)) =
      (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
          (Complex.normSq (total c) : ℂ) -
        ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
          ((Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ)) := by
  classical
  let f : ℕ → ℕ → ℂ := fun i j =>
    star (complexExtension c i) * complexExtension c j
  have hdist (i j : ℕ) (hi : i < n + 1) (hj : j < n + 1) :
      (((|realExtension t i - realExtension t j| : ℝ)) : ℂ) =
        (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) -
          ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
            (sameIndicatorNat i j k : ℂ) := by
    have h := same_gap_sum_nat t hmono hi hj
    have hc := congrArg (fun x : ℝ => (x : ℂ)) h
    rw [Complex.ofReal_sum, Complex.ofReal_sub] at hc
    simp_rw [Complex.ofReal_mul] at hc
    rw [realExtension_of_lt t hi, realExtension_of_lt t hj]
    linear_combination hc
  calc
  (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      star (complexExtension c i) * complexExtension c j *
        (((|realExtension t i - realExtension t j| : ℝ)) : ℂ)) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        f i j * ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) -
          ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
            (sameIndicatorNat i j k : ℂ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    rw [hdist i j (by simp only [Finset.mem_range] at hi; omega)
      (by simp only [Finset.mem_range] at hj; omega)]
  _ = (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
        (Complex.normSq (total c) : ℂ) -
      ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
        ((Complex.normSq (cutPrefix c k) : ℂ) +
          (Complex.normSq (cutSuffix c k) : ℂ)) := by
    have hF :
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) =
          (Complex.normSq (total c) : ℂ) := by
      simpa [f] using (normSq_total_expansion c).symm
    have hQ (k : ℕ) (hk : k < n) :
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          f i j * (sameIndicatorNat i j k : ℂ)) =
          (Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ) := by
      simpa [f] using (same_pair_expansion c hk)
    have hcomm :
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range n,
            f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ))) =
          ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
            (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              f i j * (sameIndicatorNat i j k : ℂ)) := by
      calc
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ k ∈ Finset.range n,
              f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ))) =
            ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range n,
              ∑ j ∈ Finset.range (n + 1),
                f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range (n + 1),
              ∑ j ∈ Finset.range (n + 1),
                f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ)) := by
          rw [Finset.sum_comm]
        _ = ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
              (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                f i j * (sameIndicatorNat i j k : ℂ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          calc
            (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ))) =
                ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                  (gapExtension t k : ℂ) *
                    (f i j * (sameIndicatorNat i j k : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (gapExtension t k : ℂ) *
                (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                  f i j * (sameIndicatorNat i j k : ℂ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
    calc
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          f i j * ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) -
            ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
              (sameIndicatorNat i j k : ℂ))) =
          (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
              (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) -
            ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              ∑ k ∈ Finset.range n,
                f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ)) := by
        have hfactor :
            (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                f i j * ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ))) =
              (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
                (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) := by
          calc
            (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                f i j * ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ))) =
                ∑ i ∈ Finset.range (n + 1),
                  (∑ j ∈ Finset.range (n + 1), f i j) *
                    ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_mul]
            _ =
                (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) *
                  ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ)) := by
              rw [Finset.sum_mul]
            _ = (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
                (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) := by ring
        have hexpand :
            (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                f i j * ∑ k ∈ Finset.range n,
                  (gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ)) =
              ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                ∑ k ∈ Finset.range n,
                  f i j * ((gapExtension t k : ℂ) * (sameIndicatorNat i j k : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [hfactor, hexpand]
      _ = (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
              (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) -
            ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
              (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                f i j * (sameIndicatorNat i j k : ℂ)) := by rw [hcomm]
      _ = (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
              (Complex.normSq (total c) : ℂ) -
            ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
              ((Complex.normSq (cutPrefix c k) : ℂ) +
                (Complex.normSq (cutSuffix c k) : ℂ)) := by
        rw [hF]
        apply congrArg (fun z =>
          (((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
              (Complex.normSq (total c) : ℂ) - z)
        apply Finset.sum_congr rfl
        intro k hk
        rw [hQ k (by simp only [Finset.mem_range] at hk; exact hk)]

theorem energy_identity {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) (c : Fin (n + 1) → ℂ) :
    star c ⬝ᵥ (kernel L t *ᵥ c) =
      (((L - (t (Fin.last n) - t (0 : Fin (n + 1)))) *
          Complex.normSq (total c) : ℝ) : ℂ) +
        ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
          ((Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ)) := by
  classical
  let f : ℕ → ℕ → ℂ := fun i j =>
    star (complexExtension c i) * complexExtension c j
  have hF :
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) =
        (Complex.normSq (total c) : ℂ) := by
    simpa [f] using (normSq_total_expansion c).symm
  have hfactor (a : ℂ) :
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j * a) =
        a * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) := by
    calc
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j * a) =
          ∑ i ∈ Finset.range (n + 1),
            (∑ j ∈ Finset.range (n + 1), f i j) * a := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) * a := by
        rw [Finset.sum_mul]
      _ = a * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), f i j) := by
        ring
  calc
    star c ⬝ᵥ (kernel L t *ᵥ c) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          f i j * (((L - |realExtension t i - realExtension t j| : ℝ) : ℂ)) := by
      rw [quadratic_range_expansion]
    _ = (((L : ℝ) : ℂ) * (Complex.normSq (total c) : ℂ)) -
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          f i j * (((|realExtension t i - realExtension t j| : ℝ)) : ℂ) := by
      simp_rw [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]
      rw [hfactor, hF]
    _ = (((L : ℝ) : ℂ) * (Complex.normSq (total c) : ℂ)) -
        ((((t (Fin.last n) - t (0 : Fin (n + 1))) : ℝ) : ℂ) *
          (Complex.normSq (total c) : ℂ) -
        ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
          ((Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ))) := by
      rw [pair_distance_decomposition L t hmono c]
    _ = (((L - (t (Fin.last n) - t (0 : Fin (n + 1)))) *
          Complex.normSq (total c) : ℝ) : ℂ) +
        ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
          ((Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ)) := by
      push_cast
      ring

theorem normSq_centered (z m : ℂ) :
    Complex.normSq z + Complex.normSq (m - z) =
      2 * Complex.normSq (z - m / 2) + Complex.normSq m / 2 := by
  simp [Complex.normSq_apply]
  ring

theorem energy_centered {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (hmono : Monotone t) (c : Fin (n + 1) → ℂ) :
    star c ⬝ᵥ (kernel L t *ᵥ c) =
      (((L - (t (Fin.last n) - t (0 : Fin (n + 1))) / 2) *
          Complex.normSq (total c) : ℝ) : ℂ) +
        ∑ k ∈ Finset.range n, (2 * gapExtension t k : ℂ) *
          (Complex.normSq (cutPrefix c k - total c / 2) : ℂ) := by
  rw [energy_identity L t hmono c]
  have hterm (k : ℕ) (hk : k < n) :
      (gapExtension t k : ℂ) *
          ((Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ)) =
        (2 * gapExtension t k : ℂ) *
            (Complex.normSq (cutPrefix c k - total c / 2) : ℂ) +
          (gapExtension t k : ℂ) *
            ((Complex.normSq (total c) : ℂ) / 2) := by
    have hc := normSq_centered (cutPrefix c k) (total c)
    have hc' :
        (Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (total c - cutPrefix c k) : ℂ) =
          (2 * Complex.normSq (cutPrefix c k - total c / 2) : ℂ) +
            (Complex.normSq (total c) : ℂ) / 2 := by
      exact_mod_cast hc
    rw [cut_split c hk] at hc'
    rw [hc']
    ring
  have hgap :
      (∑ k ∈ Finset.range n, (gapExtension t k : ℂ)) =
        ((t (Fin.last n) - t (0 : Fin (n + 1))) : ℂ) := by
    have hg := congrArg (fun r : ℝ => (r : ℂ)) (total_gap_sum t)
    simpa [Complex.ofReal_sum] using hg
  calc
    (((L - (t (Fin.last n) - t (0 : Fin (n + 1)))) *
          Complex.normSq (total c) : ℝ) : ℂ) +
        ∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
          ((Complex.normSq (cutPrefix c k) : ℂ) +
            (Complex.normSq (cutSuffix c k) : ℂ)) =
      (((L - (t (Fin.last n) - t (0 : Fin (n + 1))) / 2) *
          Complex.normSq (total c) : ℝ) : ℂ) +
        ∑ k ∈ Finset.range n, (2 * gapExtension t k : ℂ) *
          (Complex.normSq (cutPrefix c k - total c / 2) : ℂ) := by
      push_cast
      rw [show (∑ k ∈ Finset.range n, (gapExtension t k : ℂ) *
            ((Complex.normSq (cutPrefix c k) : ℂ) +
              (Complex.normSq (cutSuffix c k) : ℂ))) =
          ∑ k ∈ Finset.range n,
            ((2 * gapExtension t k : ℂ) *
                (Complex.normSq (cutPrefix c k - total c / 2) : ℂ) +
              (gapExtension t k : ℂ) * ((Complex.normSq (total c) : ℂ) / 2)) by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k (Finset.mem_range.mp hk)]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hgap]
      ring

theorem gapExtension_pos {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hstrict : StrictMono t) {k : ℕ} (hk : k < n) : 0 < gapExtension t k := by
  rw [gapExtension, realExtension_of_lt t (by omega),
    realExtension_of_lt t (by omega)]
  apply sub_pos.mpr
  apply hstrict
  simp only [Fin.mk_lt_mk]
  omega

theorem exists_cutPrefix_ne_zero {n : ℕ} (c : Fin (n + 1) → ℂ)
    (hc : c ≠ 0) (htotal : total c = 0) :
    ∃ k, k < n ∧ cutPrefix c k ≠ 0 := by
  by_contra h
  push_neg at h
  have hprefix : ∀ k, k < n → cutPrefix c k = 0 := h
  have hcoord : ∀ i : Fin (n + 1), c i = 0 := by
    intro i
    by_cases hi : i.val < n
    · by_cases hi0 : i.val = 0
      · have hp := hprefix 0 (by omega)
        have hi0' : i = 0 := Fin.ext hi0
        subst i
        simpa [cutPrefix, complexExtension] using hp
      · let q := i.val - 1
        have hq : q < n := by omega
        have hq0 : q + 1 = i.val := by dsimp [q]; omega
        have hpq := hprefix q hq
        have hpi := hprefix i.val hi
        have hpq' : (∑ j ∈ Finset.range i.val,
            complexExtension c j) = 0 := by
          rw [cutPrefix] at hpq
          simpa [hq0] using hpq
        have hpi' : (∑ j ∈ Finset.range (i.val + 1),
            complexExtension c j) = 0 := by
          rw [cutPrefix] at hpi
          simpa using hpi
        rw [Finset.sum_range_succ] at hpi'
        have hci : complexExtension c i.val = 0 := by
          rw [hpq'] at hpi'
          simpa [add_eq_zero_iff_eq_neg] using hpi'
        simpa [complexExtension, i.isLt] using hci
    · have hilast : i = Fin.last n := by
        apply Fin.ext
        have hiN : i.val = n := by omega
        simpa using hiN
      subst i
      have hp : (∑ j ∈ Finset.range n, complexExtension c j) = 0 := by
        by_cases hn0 : n = 0
        · simp [hn0]
        · have hpn := hprefix (n - 1) (by omega)
          rw [cutPrefix] at hpn
          have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
          rw [Nat.sub_add_cancel hn1] at hpn
          exact hpn
      have ht := htotal
      rw [total, Finset.sum_range_succ] at ht
      rw [hp] at ht
      simpa [complexExtension, Fin.last] using ht
  exact hc (funext hcoord)

theorem posdef_implies_threshold {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (hstrict : StrictMono t) (hn : 0 < n) (hP : (kernel L t).PosDef) :
    2 * L > t (Fin.last n) - t (0 : Fin (n + 1)) := by
  let e : Fin 2 → Fin (n + 1) := fun q => if q = 0 then 0 else Fin.last n
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e, hn]
  have hs := hP.submatrix he
  have hc := hs.dotProduct_mulVec_pos (x := fun _ : Fin 2 => (1 : ℂ)) (by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    simp at h0)
  simp [dotProduct, Matrix.mulVec, Matrix.submatrix, e, kernel,
    Fin.isValue, abs_sub_comm] at hc
  have hD : 0 ≤ t (Fin.last n) - t (0 : Fin (n + 1)) :=
    sub_nonneg.mpr (hstrict.monotone (Fin.zero_le _))
  have hc'' :
      ((|t (Fin.last n) - t (0 : Fin (n + 1))| +
        |t (Fin.last n) - t (0 : Fin (n + 1))| : ℝ) : ℂ) <
      ((2 * (2 * L) : ℝ) : ℂ) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_natCast] using hc
  have hc' : |t (Fin.last n) - t (0 : Fin (n + 1))| +
      |t (Fin.last n) - t (0 : Fin (n + 1))| < 2 * (2 * L) :=
    (RCLike.ofReal_lt_ofReal.mp hc'')
  rw [abs_of_nonneg hD] at hc'
  linarith

theorem threshold_posdef {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (hstrict : StrictMono t) (hL : 2 * L > t (Fin.last n) - t (0 : Fin (n + 1))) :
    (kernel L t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (kernel_hermitian L t)
  intro c hc
  rw [energy_centered L t hstrict.monotone c]
  have hD : 0 ≤ t (Fin.last n) - t (0 : Fin (n + 1)) :=
    sub_nonneg.mpr (hstrict.monotone (Fin.zero_le _))
  have hcoef : 0 < L - (t (Fin.last n) - t (0 : Fin (n + 1))) / 2 := by
    linarith
  by_cases htotal : total c = 0
  · have hcut := exists_cutPrefix_ne_zero c hc htotal
    obtain ⟨k, hk, hknz⟩ := hcut
    have hsum_pos :
        0 < ∑ k ∈ Finset.range n,
          (2 * gapExtension t k : ℂ) *
            (Complex.normSq (cutPrefix c k - total c / 2) : ℂ) := by
      apply Finset.sum_pos' (fun k hk' => by
        have hterm :
            0 ≤ ((2 * gapExtension t k *
              Complex.normSq (cutPrefix c k - total c / 2) : ℝ) : ℂ) := by
          apply RCLike.ofReal_nonneg.mpr
          exact mul_nonneg
            (mul_nonneg (by norm_num) ((gapExtension_pos t hstrict
              (Finset.mem_range.mp hk')).le))
            (Complex.normSq_nonneg _)
        simpa [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using hterm)
      refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
      rw [htotal]
      have hterm :
          0 < ((2 * gapExtension t k * Complex.normSq (cutPrefix c k) : ℝ) : ℂ) := by
        apply RCLike.ofReal_pos.mpr
        exact mul_pos
          (mul_pos (by norm_num) (gapExtension_pos t hstrict hk))
          (Complex.normSq_pos.mpr hknz)
      simpa [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using hterm
    have hmain :
        (((L - (t (Fin.last n) - t (0 : Fin (n + 1))) / 2) *
          Complex.normSq (total c) : ℝ) : ℂ) = 0 := by
      simp [htotal]
    rw [hmain, zero_add]
    exact hsum_pos
  · have hmain :
        0 < (((L - (t (Fin.last n) - t (0 : Fin (n + 1))) / 2) *
          Complex.normSq (total c) : ℝ) : ℂ) := by
      apply RCLike.ofReal_pos.mpr
      exact mul_pos hcoef (Complex.normSq_pos.mpr htotal)
    have hsum_nonneg :
        0 ≤ ∑ k ∈ Finset.range n,
          (2 * gapExtension t k : ℂ) *
            (Complex.normSq (cutPrefix c k - total c / 2) : ℂ) := by
      apply Finset.sum_nonneg
      intro k hk'
      have hterm :
          0 ≤ ((2 * gapExtension t k *
            Complex.normSq (cutPrefix c k - total c / 2) : ℝ) : ℂ) := by
        apply RCLike.ofReal_nonneg.mpr
        exact mul_nonneg
          (mul_nonneg (by norm_num) ((gapExtension_pos t hstrict
            (Finset.mem_range.mp hk')).le))
          (Complex.normSq_nonneg _)
      simpa [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using hterm
    exact add_pos_of_pos_of_nonneg hmain hsum_nonneg

theorem posdef_iff_threshold {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ)
    (hstrict : StrictMono t) :
    (kernel L t).PosDef ↔ 2 * L > t (Fin.last n) - t (0 : Fin (n + 1)) := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst n
      have hd := h.diag_pos (i := (0 : Fin 1))
      simpa [kernel] using hd
    · exact posdef_implies_threshold L t hstrict (Nat.pos_of_ne_zero hn) h
  · exact threshold_posdef L t hstrict

end D5.S3.Weil.PrimeKernel.OrderedAffineDistance
