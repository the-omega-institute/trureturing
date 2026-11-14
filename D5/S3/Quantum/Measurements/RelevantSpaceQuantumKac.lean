/- GID: D5/S3/Quantum/Measurements/RelevantSpaceQuantumKac
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/RelevantSpaceQuantumKac
   mirror-E: none(waiver:finite-dimensional-operator-theorem)
   anchors: []
   utility: none
   digest: Projection monitoring preserves the original Kraus reachable space. -/

import D5.S3.Quantum.Measurement.PositiveBranchReachableResponse

/-! Kraus words and projection monitoring on their actual reachable space. -/

noncomputable section

open Matrix
open D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n : Type*} {α : Type} [Fintype n] [DecidableEq n]

private theorem reachable_le_of_invariant (K : α → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (hρ : matrixSupport ρ ≤ S)
    (hK : ∀ a, ∀ v ∈ S, (K a).toEuclideanLin v ∈ S) :
    reachableSpace K ρ ≤ S := by
  apply iSup_le
  intro l
  apply Submodule.span_le.mpr
  rintro y ⟨w, _hw, v, hv, rfl⟩
  have hw : ∀ w : List α, (krausWord K w).toEuclideanLin v ∈ S := by
    intro w
    induction w with
    | nil => simpa [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one] using hρ hv
    | cons a w ih =>
        simpa only [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
          LinearMap.comp_apply] using hK a _ ih
  exact hw w

/-- The original Kraus family and its actual no-return branches generate the
same reachable space. This holds for every Hermitian initial matrix `P`;
the pure-state projection case is Appendix A, equation (A9). -/
theorem monitored_reachable_space_eq (K : α → Matrix n n ℂ)
    (P : Matrix n n ℂ) (hP : P.IsHermitian) :
    reachableSpace (fun a => (1 - P) * K a) P = reachableSpace K P := by
  have hinitial (J : α → Matrix n n ℂ) : matrixSupport P ≤ reachableSpace J P := by
    apply le_iSup_of_le 0
    intro v hv
    exact Submodule.subset_span ⟨[], by simp, v, hv,
      by simp [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one]⟩
  have hPmap (J : α → Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
      P.toEuclideanLin v ∈ reachableSpace J P := by
    apply hinitial J
    rw [matrixSupport_eq_range hP]
    exact ⟨v, rfl⟩
  apply le_antisymm
  · apply reachable_le_of_invariant _ _ _ (hinitial K)
    intro a v hv
    have hKv := reachable_kraus_invariant K P a v hv
    have hsub := (reachableSpace K P).sub_mem hKv (hPmap K ((K a).toEuclideanLin v))
    simpa only [sub_mul, one_mul, map_sub, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.sub_apply, LinearMap.comp_apply] using hsub
  · apply reachable_le_of_invariant _ _ _ (hinitial (fun a => (1 - P) * K a))
    intro a v hv
    have hQv := reachable_kraus_invariant (fun a => (1 - P) * K a) P a v hv
    have hsum := (reachableSpace (fun a => (1 - P) * K a) P).add_mem hQv
      (hPmap (fun a => (1 - P) * K a) ((K a).toEuclideanLin v))
    simpa only [sub_mul, one_mul, map_sub, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.sub_apply, LinearMap.comp_apply,
      sub_add_cancel] using hsum

#print axioms monitored_reachable_space_eq

end D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
