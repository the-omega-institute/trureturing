/- GID: D5/S3/Quantum/Dynamics/PositiveSectionCentralSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PositiveSectionCentralSupport
   mirror-E: none(waiver:finite-block-positive-sections)
   anchors: []
   utility: none
   digest: Global positive linear sections preserve the source central decomposition. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ComplexOrder
namespace D5.S3.Quantum.Dynamics.PositiveSectionCentralSupport

/-- A zero projected trace of a positive matrix annihilates that entire corner. -/
private theorem annihilates_of_zero_projected_trace
    {n : Type*} [Fintype n] [DecidableEq n]
    (B Q : Matrix n n ℂ) (hB : B.PosSemidef)
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (htr : Matrix.trace (Q * B) = 0) :
    B * Q = 0 ∧ Q * B = 0 := by
  have hcompressed : Qᴴ * B * Q = 0 := by
    apply (hB.conjTranspose_mul_mul_same Q).trace_eq_zero_iff.mp
    rw [hQ.eq, Matrix.trace_mul_cycle, hQQ, htr]
  have hright : B * Q = 0 := by
    ext i j
    let x : n → ℂ := fun k => Q k j
    have hquadratic : star x ⬝ᵥ B *ᵥ x = 0 := by
      have hz := congrArg (fun C : Matrix n n ℂ => C j j) hcompressed
      simpa [x, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc] using hz
    have hzero := hB.dotProduct_mulVec_zero_iff.mp hquadratic
    simpa [x, Matrix.mulVec, Matrix.mul_apply, dotProduct] using congrFun hzero i
  refine ⟨hright, ?_⟩
  have hz := congrArg Matrix.conjTranspose hright
  simpa only [Matrix.conjTranspose_mul, hQ.eq, hB.isHermitian.eq,
    Matrix.conjTranspose_zero] using hz

/-- Positive sections of a trace-dual block extraction have no cross-central angles.
The coarse carrier is the whole finite direct sum; no normalization or complete
positivity is imposed on the section. Empty matrix blocks are allowed. -/
theorem positive_section_central_support
    {S n : Type*} [Fintype S] [DecidableEq S] [Fintype n] [DecidableEq n]
    (C : S → Type*) [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]
    (E : Matrix n n ℂ →ₗ[ℂ] (∀ s, Matrix (C s) (C s) ℂ))
    (R : (∀ s, Matrix (C s) (C s) ℂ) →ₗ[ℂ] Matrix n n ℂ)
    (Q : S → Matrix n n ℂ)
    (hQ : ∀ s, (Q s).IsHermitian)
    (hQQ : ∀ s, Q s * Q s = Q s)
    (hcover : ∑ s, Q s = 1)
    (hdual : ∀ B s, Matrix.trace (Q s * B) = Matrix.trace ((E B) s))
    (hER : ∀ X, E (R X) = X)
    (hpositive : ∀ X, (∀ s, (X s).PosSemidef) → (R X).PosSemidef)
    (ρ : ∀ s, Matrix (C s) (C s) ℂ) (hρ : ∀ s, (ρ s).PosSemidef) :
    R ρ = ∑ s, Q s * R ρ * Q s := by
  classical
  let X : S → (∀ s, Matrix (C s) (C s) ℂ) := fun s => Pi.single s (ρ s)
  let B : S → Matrix n n ℂ := fun s => R (X s)
  have hB (s : S) : (B s).PosSemidef := by
    apply hpositive
    intro r
    by_cases hrs : r = s
    · subst r
      simpa [X] using hρ s
    · simpa [X, Pi.single_eq_of_ne hrs] using
        (Matrix.PosSemidef.zero : (0 : Matrix (C r) (C r) ℂ).PosSemidef)
  have hoff (s r : S) (hrs : r ≠ s) :
      B s * Q r = 0 ∧ Q r * B s = 0 := by
    apply annihilates_of_zero_projected_trace (B s) (Q r) (hB s) (hQ r) (hQQ r)
    rw [hdual]
    change Matrix.trace ((E (R (X s))) r) = 0
    rw [hER]
    simp [X, Pi.single_eq_of_ne hrs]
  have hleft (s : S) : Q s * B s = B s := by
    calc
      Q s * B s = ∑ r, Q r * B s := by
        symm
        apply Finset.sum_eq_single s
        · intro r _ hrs
          exact (hoff s r hrs).2
        · simp
      _ = (∑ r, Q r) * B s := (Finset.sum_mul ..).symm
      _ = B s := by rw [hcover, one_mul]
  have hright (s : S) : B s * Q s = B s := by
    calc
      B s * Q s = ∑ r, B s * Q r := by
        symm
        apply Finset.sum_eq_single s
        · intro r _ hrs
          exact (hoff s r hrs).1
        · simp
      _ = B s * (∑ r, Q r) := (Finset.mul_sum ..).symm
      _ = B s := by rw [hcover, mul_one]
  have hpinch (s : S) : (∑ r, Q r * B s * Q r) = B s := by
    calc
      (∑ r, Q r * B s * Q r) = Q s * B s * Q s := by
        apply Finset.sum_eq_single s
        · intro r _ hrs
          rw [(hoff s r hrs).2, zero_mul]
        · simp
      _ = B s := by rw [hleft, hright]
  have hsum : (∑ s, X s) = ρ := by
    ext s i j
    simp [X, Pi.single_apply]
  have hRsum : (∑ s, B s) = R ρ := by
    change (∑ s, R (X s)) = R ρ
    rw [← map_sum, hsum]
  calc
    R ρ = ∑ s, B s := hRsum.symm
    _ = ∑ s, ∑ r, Q r * B s * Q r := by simp_rw [hpinch]
    _ = ∑ r, ∑ s, Q r * B s * Q r := Finset.sum_comm
    _ = ∑ r, Q r * (∑ s, B s) * Q r := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ r, Q r * R ρ * Q r := by rw [hRsum]

#print axioms positive_section_central_support
end D5.S3.Quantum.Dynamics.PositiveSectionCentralSupport
