/- GID: D5/S3/Quantum/Information/ClassicalConditionalCopy
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ClassicalConditionalCopy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical conditional copies over a finite classical pointer. -/

import D5.S3.Quantum.Information.StrongSubadditivity

set_option autoImplicit false

open scoped BigOperators Kronecker MatrixOrder ComplexOrder CStarAlgebra
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Entropy.MaxEntropy

namespace D5.S3.Quantum.Information.ClassicalConditionalCopy

variable {X B C : Type*} [Fintype X] [DecidableEq X]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem recordState_entry (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState B) (x y : X) (b c : B) :
    CStarMatrix.ofMatrix.symm (recordState p hp hs tau).1 (x, b) (y, c) =
      if x = y then (p x : ℂ) * CStarMatrix.ofMatrix.symm (tau x).1 b c else 0 := by
  classical
  change (∑ i, p i • ((Matrix.diagonal (fun j : X => if j = i then (1 : ℂ) else 0))
      ⊗ₖ CStarMatrix.ofMatrix.symm (tau i).1) :
    Matrix (X × B) (X × B) ℂ) (x, b) (y, c) = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    Matrix.diagonal_apply, Complex.real_smul]
  by_cases h : x = y
  · subst y
    simp [eq_comm]
  · simp [h]

/-- Trace the last fragment of a CQ record, retaining its complete classical pointer. -/
theorem recordState_traceRight
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState (B × C)) :
    marginalRight (relabelState (Equiv.prodAssoc X B C) (recordState p hp hs tau)) =
      recordState p hp hs (fun x => marginalRight (tau x)) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨x, b⟩ ⟨y, c⟩
  change (∑ z, CStarMatrix.ofMatrix.symm
    (recordState p hp hs tau).1 (x, (b, z)) (y, (c, z))) = _
  simp only [recordState_entry]
  by_cases h : x = y
  · simp only [h, ite_true]
    exact (Finset.mul_sum _ _ _).symm
  · simp [h]

/-- Move the middle fragment behind the copy before taking its actual partial trace. -/
def middleSwap : ((X × C) × B) ≃ (X × (B × C)) where
  toFun q := (q.1.1, (q.2, q.1.2))
  invFun q := ((q.1, q.2.2), q.2.1)
  left_inv := by rintro ⟨⟨x, c⟩, b⟩; rfl
  right_inv := by rintro ⟨x, b, c⟩; rfl

theorem recordState_traceMiddle
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState (B × C)) :
    marginalRight (relabelState middleSwap (recordState p hp hs tau)) =
      recordState p hp hs (fun x => marginalLeft (tau x)) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨x, b⟩ ⟨y, c⟩
  change (∑ z, CStarMatrix.ofMatrix.symm
    (recordState p hp hs tau).1 (x, (z, b)) (y, (z, c))) = _
  simp only [recordState_entry]
  by_cases h : x = y
  · simp only [h, ite_true]
    exact (Finset.mul_sum _ _ _).symm
  · simp [h]

/-- The copy is independent of BC inside each pointer block; BC itself is arbitrary. -/
noncomputable def conditionalCopy
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState (B × C)) : DensityState (X × ((B × C) × C)) :=
  recordState p hp hs (fun x => productState (tau x) (marginalLeft (tau x)))

/-- The constructed copy has exactly the original XBC density matrix after discarding E. -/
theorem conditionalCopy_discard
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState (B × C)) :
    marginalRight (relabelState (Equiv.prodAssoc X (B × C) C)
      (conditionalCopy p hp hs tau)) = recordState p hp hs tau := by
  rw [conditionalCopy, recordState_traceRight]
  simp only [marginalRight_productState]

/-- The XE marginal is the original XC marginal with E taking C's index type. -/
theorem conditionalCopy_pointer_copy
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState (B × C)) :
    marginalRight (relabelState middleSwap (conditionalCopy p hp hs tau)) =
      recordState p hp hs (fun x => marginalLeft (tau x)) := by
  rw [conditionalCopy, recordState_traceMiddle]
  simp only [marginalLeft_productState]

theorem entropy_record_pointer
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState B) :
    vonNeumannEntropy (marginalRight (recordState p hp hs tau)) = shannonEntropy p := by
  rw [recordState, marginalRight_mixture]
  simp only [marginalRight_productState]
  rw [orthogonal_mixture_entropy p hp hs pointerState pointerState_orthogonal]
  simp only [entropy_pointerState, mul_zero, Finset.sum_const_zero, add_zero]

/-- Exact copy entropy with arbitrary singular and entangled conditional BC blocks. -/
theorem entropy_conditionalCopy
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : X → DensityState (B × C)) :
    vonNeumannEntropy (conditionalCopy p hp hs tau) =
      vonNeumannEntropy (recordState p hp hs tau) +
        vonNeumannEntropy (recordState p hp hs (fun x => marginalLeft (tau x))) -
          shannonEntropy p := by
  simp only [conditionalCopy, entropy_recordState, vonNeumannEntropy_productState]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

#print axioms conditionalCopy_discard
#print axioms conditionalCopy_pointer_copy
#print axioms entropy_conditionalCopy

end D5.S3.Quantum.Information.ClassicalConditionalCopy
