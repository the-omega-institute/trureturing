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

def total {n : ℕ} (c : Fin (n + 1) → ℂ) : ℂ := ∑ i, c i

def prefixSum {n : ℕ} (c : Fin (n + 1) → ℂ) (k : Fin n) : ℂ :=
  ∑ i ∈ Finset.Iic (Fin.castSucc k), c i

def realExtension {n : ℕ} (t : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n + 1 then t ⟨k, hk⟩ else 0

def complexExtension {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) : ℂ :=
  if hk : k < n + 1 then c ⟨k, hk⟩ else 0

def gapExtension {n : ℕ} (t : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  realExtension t (k + 1) - realExtension t k

def cutPrefix {n : ℕ} (c : Fin (n + 1) → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), complexExtension c j

theorem realExtension_of_lt {n : ℕ} (t : Fin (n + 1) → ℝ) {k : ℕ}
    (hk : k < n + 1) : realExtension t k = t ⟨k, hk⟩ := by
  simp [realExtension, hk]

theorem complexExtension_of_lt {n : ℕ} (c : Fin (n + 1) → ℂ) {k : ℕ}
    (hk : k < n + 1) : complexExtension c k = c ⟨k, hk⟩ := by
  simp [complexExtension, hk]

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

theorem kernel_hermitian {n : ℕ} (L : ℝ) (t : Fin (n + 1) → ℝ) :
    (kernel L t).IsHermitian := by
  ext i j
  simp [Matrix.IsHermitian, kernel, abs_sub_comm]

end D5.S3.Weil.PrimeKernel.OrderedAffineDistance
