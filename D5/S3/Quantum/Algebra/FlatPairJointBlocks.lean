/- GID: D5/S3/Quantum/Algebra/FlatPairJointBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FlatPairJointBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-space circle and quaternionic frames for a flat skew pair. -/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Complete original-vector block specification. -/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.FlatPairJointBlocks

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A complete orthonormal frame on the given space, grouped into circle and
quaternionic blocks. Parameters vary independently from block to block. Empty
index sets include the zero space. The quaternionic frame is ordered as
`q, J₁ q, J₂ q, J₁ J₂ q`. -/
def HasFlatPairJointBlocks (A D : F →ₗ[ℝ] F) : Prop :=
  ∃ (c h : ℕ)
    (b : OrthonormalBasis ((Fin c × Fin 2) ⊕ (Fin h × Fin 4)) ℝ F)
    (a d : Fin c → ℝ) (lam t : Fin h → ℝ),
    (∀ i, a i ^ 2 + d i ^ 2 = 1 ∧
      A (b (.inl (i, 0))) = a i • b (.inl (i, 1)) ∧
      A (b (.inl (i, 1))) = -(a i) • b (.inl (i, 0)) ∧
      D (b (.inl (i, 0))) = d i • b (.inl (i, 1)) ∧
      D (b (.inl (i, 1))) = -(d i) • b (.inl (i, 0))) ∧
    (∀ i, 0 < lam i ∧ lam i < 1 ∧ -1 < t i ∧ t i < 1 ∧
      A (b (.inr (i, 0))) = Real.sqrt (lam i) • b (.inr (i, 1)) ∧
      A (b (.inr (i, 1))) = -Real.sqrt (lam i) • b (.inr (i, 0)) ∧
      A (b (.inr (i, 2))) = Real.sqrt (lam i) • b (.inr (i, 3)) ∧
      A (b (.inr (i, 3))) = -Real.sqrt (lam i) • b (.inr (i, 2)) ∧
      D (b (.inr (i, 0))) = Real.sqrt (1 - lam i) •
        (t i • b (.inr (i, 1)) + Real.sqrt (1 - t i ^ 2) • b (.inr (i, 2))) ∧
      D (b (.inr (i, 1))) = Real.sqrt (1 - lam i) •
        (-(t i) • b (.inr (i, 0)) - Real.sqrt (1 - t i ^ 2) • b (.inr (i, 3))) ∧
      D (b (.inr (i, 2))) = Real.sqrt (1 - lam i) •
        (t i • b (.inr (i, 3)) - Real.sqrt (1 - t i ^ 2) • b (.inr (i, 0))) ∧
      D (b (.inr (i, 3))) = Real.sqrt (1 - lam i) •
        (-(t i) • b (.inr (i, 2)) + Real.sqrt (1 - t i ^ 2) • b (.inr (i, 1))))

end D5.S3.Quantum.Algebra.FlatPairJointBlocks
