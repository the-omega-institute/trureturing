/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Identity padding preserves TNN minors and split products. -/

/- Mathematical classification:
   tnn_padOne:
     proof_shape: content
     escape_witness: conclusion: ordered-minor decomposition by the two first-index selections
   tnn_padLeft:
     proof_shape: content
     escape_witness: tnn_padOne: arbitrary-length padding induction
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsBlock

open Finset Matrix Equiv
namespace PSW
open scoped Classical

/-- A single identity entry adjoined before the original matrix. -/
def padOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => A i j) j) i

private def predEmbedding {k n : ℕ} (r : Fin k ↪o Fin (n + 1))
    (hr : ∀ i, 0 < (r i).val) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨(r i).val - 1, by have hi := (r i).isLt; have hp := hr i; omega⟩)
    (by intro i j hij; have hh := r.strictMono hij; have hp := hr i; have hq := hr j; change (r i).val - 1 < (r j).val - 1; omega)

private def tailEmbedding {k n : ℕ} (r : Fin (k + 1) ↪o Fin (n + 1)) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨(r i.succ).val - 1, by
    have hi := (r i.succ).isLt
    have hh := r.strictMono (Fin.succ_pos i)
    omega⟩) (by
    intro i j hij
    have hh := r.strictMono (Fin.succ_lt_succ_iff.mpr hij)
    have hp := r.strictMono (Fin.succ_pos i)
    change (r i.succ).val - 1 < (r j.succ).val - 1
    omega)

/-- Identity padding preserves every literal ordered square minor. -/
theorem tnn_padOne {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A) : TNN (padOne A) := by
  have padOne_pred {k n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
      (r c : Fin k ↪o Fin (n + 1)) (hr : ∀ i, 0 < (r i).val) (hc : ∀ j, 0 < (c j).val) :
      (padOne A).submatrix r c = A.submatrix (predEmbedding r hr) (predEmbedding c hc) := by
    ext i j
    have hri : (predEmbedding r hr i).succ = r i := by
      apply Fin.ext; simp [predEmbedding, OrderEmbedding.ofStrictMono]; have hh := hr i; omega
    have hcj : (predEmbedding c hc j).succ = c j := by
      apply Fin.ext; simp [predEmbedding, OrderEmbedding.ofStrictMono]; have hh := hc j; omega
    simp only [Matrix.submatrix_apply]
    rw [← hri, ← hcj]
    rfl
  intro k r c
  cases k with
  | zero => simp [Matrix.det_isEmpty]
  | succ k =>
    by_cases hr0 : r 0 = 0
    · by_cases hc0 : c 0 = 0
      · have hminor : ((padOne A).submatrix r c).det = (A.submatrix (tailEmbedding r) (tailEmbedding c)).det := by
          rw [Matrix.det_succ_row_zero]
          rw [Finset.sum_eq_single (0 : Fin (k + 1))]
          · have h00 : padOne A (0 : Fin (n + 1)) 0 = 1 := rfl
            simp only [Fin.val_zero, pow_zero, one_mul, Matrix.submatrix_apply, hr0, hc0, h00]
            simp only [one_mul, Fin.succAbove_zero]
            congr 1
            ext i j
            have hri : (tailEmbedding r i).succ = r i.succ := by
              apply Fin.ext
              simp [tailEmbedding, OrderEmbedding.ofStrictMono]
              have hh := r.strictMono (Fin.succ_pos i); omega
            have hcj : (tailEmbedding c j).succ = c j.succ := by
              apply Fin.ext
              simp [tailEmbedding, OrderEmbedding.ofStrictMono]
              have hh := c.strictMono (Fin.succ_pos j); omega
            simp only [Matrix.submatrix_apply]
            rw [← hri, ← hcj]
            rfl
          · intro j _ hj
            have hcj : c j ≠ 0 := by intro he; exact hj (c.injective (he.trans hc0.symm))
            obtain ⟨j', hj'⟩ := Fin.eq_succ_of_ne_zero hcj
            have h0s : padOne A (0 : Fin (n + 1)) j'.succ = 0 := rfl
            simp only [Matrix.submatrix_apply, hr0, hj', h0s, mul_zero, zero_mul]
          · simp
        rw [hminor]
        exact hA k (tailEmbedding r) (tailEmbedding c)
      · have hzero : ((padOne A).submatrix r c).det = 0 := by
          apply Matrix.det_eq_zero_of_row_eq_zero 0
          intro j
          have hcj : c j ≠ 0 := by
            intro he
            have hmon : c 0 ≤ c j := c.monotone (Fin.zero_le _)
            rw [he] at hmon
            have : c 0 = 0 := le_antisymm hmon (Fin.zero_le _)
            exact hc0 this
          obtain ⟨j', hj'⟩ := Fin.eq_succ_of_ne_zero hcj
          rw [Matrix.submatrix_apply, hr0, hj']
          rfl
        rw [hzero]
    · by_cases hc0 : c 0 = 0
      · have hzero : ((padOne A).submatrix r c).det = 0 := by
          apply Matrix.det_eq_zero_of_column_eq_zero 0
          intro i
          have hri : r i ≠ 0 := by
            intro he
            have hmon : r 0 ≤ r i := r.monotone (Fin.zero_le _)
            rw [he] at hmon
            exact hr0 (le_antisymm hmon (Fin.zero_le _))
          obtain ⟨i', hi'⟩ := Fin.eq_succ_of_ne_zero hri
          rw [Matrix.submatrix_apply, hc0, hi']
          rfl
        rw [hzero]
      · have hr : ∀ i, 0 < (r i).val := by
          intro i
          have hmon : r 0 ≤ r i := r.monotone (Fin.zero_le _)
          have hrpos : 0 < (r 0).val := by
            have hrval : (r 0).val ≠ 0 := fun h => hr0 (Fin.ext h)
            omega
          omega
        have hc : ∀ j, 0 < (c j).val := by
          intro j
          have hmon : c 0 ≤ c j := c.monotone (Fin.zero_le _)
          have hcpos : 0 < (c 0).val := by
            have hcval : (c 0).val ≠ 0 := fun h => hc0 (Fin.ext h)
            omega
          omega
        rw [padOne_pred A r c hr hc]
        exact hA (k + 1) (predEmbedding r hr) (predEmbedding c hc)

/-- Repeated first-position identity padding; its order is `n+d`. -/
def padLeft {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ∀ d : ℕ, Matrix (Fin (n + d)) (Fin (n + d)) ℝ
  | 0 => A
  | d + 1 => padOne (padLeft A d)

theorem tnn_padLeft {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A) (d : ℕ) : TNN (padLeft A d) := by
  induction d with
  | zero => exact hA
  | succ d ih => exact tnn_padOne ih

#print axioms tnn_padOne
#print axioms tnn_padLeft
end PSW
