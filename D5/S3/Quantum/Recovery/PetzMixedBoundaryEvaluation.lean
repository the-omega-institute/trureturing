/- GID: D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed Stinespring boundary entries share a frequency and admit logistic evaluation. -/

import D5.S3.Analytic.PetzLogisticEvaluation
import D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

/-!
The two terms after removing the input phases in Yang (arXiv:2609.33815v2,
Theorem II.1) have a shared frequency in each mixed output matrix entry.
The first term varies the source eigenvalue and the second varies the
reference eigenvalue. The carriers retain eigenvalue multiplicity.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
open ExponentialGramWeightedEvaluation (exponentialSum frequency)
open PetzExponentialBoundaryEvaluation (distinctFrequencies petzWeight petzWeight_pos)
open private frobenius_sq sum_evaluations from
  D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation

namespace D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation

section MixedEntries

variable {k l e : Type*} [Fintype k] [Fintype l] [Fintype e]
  [DecidableEq k] [DecidableEq l] [DecidableEq e]

private def mixedFrequency (p : k → ℝ) (q : l → ℝ) (i : l) (j : k) : k ⊕ l → ℝ
  | .inl j' => Real.log (p j') - Real.log (q i)
  | .inr i' => Real.log (p j) - Real.log (q i')

/-- Number of distinct levels represented by a finite spectral family. -/
def levelCount {i : Type*} [Fintype i] (p : i → ℝ) : ℕ :=
  (distinctFrequencies p).card

omit [DecidableEq k] [DecidableEq l] in
private theorem mixedFrequency_card (p : k → ℝ) (q : l → ℝ) (i : l) (j : k) :
    (distinctFrequencies (mixedFrequency p q i j)).card ≤ levelCount p + levelCount q - 1 := by
  classical
  let a (x : ℝ) := Real.log x - Real.log (q i)
  let b (x : ℝ) := Real.log (p j) - Real.log x
  let P := (distinctFrequencies p).image a
  let Q := (distinctFrequencies q).image b
  have hUnion : distinctFrequencies (mixedFrequency p q i j) = P ∪ Q := by
    ext x
    simp only [P, Q, distinctFrequencies, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_union, exists_exists_eq_and]
    constructor
    · rintro ⟨z | z, hz⟩
      · exact Or.inl ⟨z, hz⟩
      · exact Or.inr ⟨z, hz⟩
    · rintro (⟨z, hz⟩ | ⟨z, hz⟩)
      · exact ⟨.inl z, hz⟩
      · exact ⟨.inr z, hz⟩
  have hCommon : a (p j) ∈ P ∩ Q := by
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_image.mpr ⟨p j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, rfl⟩,
      Finset.mem_image.mpr ⟨q i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩⟩
  have hP : P.card ≤ levelCount p := Finset.card_image_le
  have hQ : Q.card ≤ levelCount q := Finset.card_image_le
  have hI := Finset.card_pos.mpr ⟨_, hCommon⟩
  have h := Finset.card_union_add_card_inter P Q
  rw [hUnion]
  omega

private def diagonalPhase {s : Type*} [DecidableEq s] (p : s → ℝ) (z : ℂ) :
    Matrix s s ℂ := diagonal (fun i => Complex.exp ((Real.log (p i) : ℂ) * z))

/-- The two output products in the reference-left, source-right eigenbasis.
The second components of row and column indices belong to the same environment. -/
def mixedBoundary (p : k → ℝ) (q : l → ℝ)
    (X : Matrix (k × e) (k × e) ℂ) (Y : Matrix (l × e) (l × e) ℂ)
    (C : Matrix (l × e) (k × e) ℂ) (t : ℝ) : Matrix (l × e) (k × e) ℂ :=
  let z := (t : ℂ) * Complex.I
  let h := ((1 / 2 : ℝ) : ℂ)
  let P (w : ℂ) : Matrix (k × e) (k × e) ℂ := diagonalPhase (p ∘ Prod.fst) w
  let Q (w : ℂ) : Matrix (l × e) (l × e) ℂ := diagonalPhase (q ∘ Prod.fst) w
  Q (-z) * C * P z * X - Y * Q (-h - z) * C * P (h + z)

private theorem mixedBoundary_entry (p : k → ℝ) (q : l → ℝ)
    (X : Matrix (k × e) (k × e) ℂ) (Y : Matrix (l × e) (l × e) ℂ)
    (C : Matrix (l × e) (k × e) ℂ) (i : l × e) (j : k × e) (t : ℝ) :
    mixedBoundary p q X Y C t i j =
      exponentialSum (mixedFrequency p q i.1 j.1)
        (Sum.elim
          (fun k' => ∑ v : e, C i (k', v) * X (k', v) j)
          (fun l' => -(∑ v : e, Y i (l', v) * C (l', v) j) *
            Complex.exp ((Real.log (p j.1) : ℂ) * ((1 / 2 : ℝ) : ℂ) -
              (Real.log (q l') : ℂ) * ((1 / 2 : ℝ) : ℂ))))
        (t : ℂ) := by
  let h : ℂ := ((1 / 2 : ℝ) : ℂ)
  let z : ℂ := (t : ℂ) * Complex.I
  let pz : Matrix (k × e) (k × e) ℂ := diagonalPhase (p ∘ Prod.fst) z
  let qz : Matrix (l × e) (l × e) ℂ := diagonalPhase (q ∘ Prod.fst) (-z)
  let ph : Matrix (k × e) (k × e) ℂ := diagonalPhase (p ∘ Prod.fst) (h + z)
  let qh : Matrix (l × e) (l × e) ℂ := diagonalPhase (q ∘ Prod.fst) (-h - z)
  have hmode (p q : ℝ) :
      Complex.exp (Complex.I * ((Real.log p - Real.log q : ℝ) : ℂ) * (t : ℂ)) =
        Complex.exp ((Real.log q : ℂ) * (-z)) * Complex.exp ((Real.log p : ℂ) * z) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp only [z]
    push_cast
    ring
  have hupper (p q : ℝ) :
      Complex.exp ((Real.log p : ℂ) * h - (Real.log q : ℂ) * h) *
        Complex.exp (Complex.I * ((Real.log p - Real.log q : ℝ) : ℂ) * (t : ℂ)) =
      Complex.exp ((Real.log q : ℂ) * (-h - z)) *
        Complex.exp ((Real.log p : ℂ) * (h + z)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp only [z]
    push_cast
    ring
  change (qz * C * pz * X) i j - (Y * qh * C * ph) i j = _
  simp only [exponentialSum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    frequency, mixedFrequency, neg_mul, Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg]
  apply congrArg₂ (· - ·)
  · rw [Matrix.mul_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k' _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    simp only [pz, qz, diagonalPhase, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Function.comp_apply, hmode]
    ring
  · rw [show (Y * qh * C * ph) i j =
        (∑ s : l × e, (Y * qh) i s * C s j) *
          Complex.exp ((Real.log (p j.1) : ℂ) * (h + z)) by
        rw [show ph = diagonal (fun s : k × e =>
          Complex.exp ((Real.log (p s.1) : ℂ) * (h + z))) from rfl,
          Matrix.mul_diagonal, Matrix.mul_apply]]
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l' _
    rw [Finset.sum_mul, mul_assoc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    simp only [qh, diagonalPhase, Matrix.mul_diagonal, Function.comp_apply]
    change _ = (Y i (l', v) * C (l', v) j) *
      (Complex.exp ((Real.log (p j.1) : ℂ) * h - (Real.log (q l') : ℂ) * h) *
        Complex.exp (Complex.I * ((Real.log (p j.1) - Real.log (q l') : ℝ) : ℂ) * (t : ℂ)))
    rw [hupper]
    ring

/-- Logistic evaluation counts distinct levels in the two spectral families. -/
theorem mixedBoundary_evaluation
    (p : k → ℝ) (q : l → ℝ)
    (X : Matrix (k × e) (k × e) ℂ) (Y : Matrix (l × e) (l × e) ℂ)
    (C : Matrix (l × e) (k × e) ℂ) :
    let H := mixedBoundary p q X Y C
    Integrable (fun t => petzWeight t * ‖H t‖ ^ 2) ∧
      ‖H 0‖ ^ 2 ≤ ((levelCount p + levelCount q - 1 : ℕ) : ℝ) *
        ∫ t : ℝ, petzWeight t * ‖H t‖ ^ 2 := by
  dsimp only
  let H := mixedBoundary p q X Y C
  have hs (t : ℝ) : ‖H t‖ ^ 2 = ∑ ij : (l × e) × (k × e), ‖H t ij.1 ij.2‖ ^ 2 := by
    rw [frobenius_sq]
    exact (Fintype.sum_prod_type (fun ij : (l × e) × (k × e) => ‖H t ij.1 ij.2‖ ^ 2)).symm
  change Integrable (fun t => petzWeight t * ‖H t‖ ^ 2) ∧
    ‖H 0‖ ^ 2 ≤ ((levelCount p + levelCount q - 1 : ℕ) : ℝ) *
      ∫ t : ℝ, petzWeight t * ‖H t‖ ^ 2
  simp only [hs, Finset.mul_sum]
  refine sum_evaluations _ _ _ (fun ij : (l × e) × (k × e) => ?_)
  simp only [H, mixedBoundary_entry, Complex.ofReal_zero]
  obtain ⟨hi, hb⟩ := PetzLogisticEvaluation.weighted_evaluation (mixedFrequency p q ij.1.1 ij.2.1) _
  exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (mixedFrequency_card p q ij.1.1 ij.2.1))
    (integral_nonneg (fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _))))⟩

end MixedEntries

end D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
