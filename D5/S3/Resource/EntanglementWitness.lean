/- GID: D5/S3/Resource/EntanglementWitness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove separable-cone convexity; witness existence remains open. -/

import Mathlib
import D5.S3.Resource.CompositeCones
import D5.S3.Resource.CompositeConeDuality

/- Provenance: Native proof over pinned mathlib. -/
/- Search receipt (2026-08-13): searched local D5 declarations for the cone
   definitions and duality (hits: `separableCone`, `blockPositive`,
   `blockPositive_iff_forall_separable_pairing_nonneg`); searched pinned mathlib
   `Analysis/Convex/Cone` (hits: `ProperCone.hyperplane_separation'`,
   `ProperCone.hyperplane_separation_point`, `ConvexCone`, `IsClosed`, and
   finite-dimensional infrastructure; miss: a closedness theorem for this
   finite-sum Kronecker cone and a ready-made Hermitian-matrix Riesz pairing).
   Consequently this file proves the cone and convexity portion only. The
   unconditional witness statement
   `R.PosSemidef -> ¬ separableCone R -> ∃ W, blockPositive W ∧ pairing R W < 0`
   remains open until that closedness-and-pairing bridge is formalized. -/

namespace D5.S3.Resource.EntanglementWitness

open D5.S3.Resource.CompositeCones
open scoped Kronecker
open scoped ComplexOrder

variable {m n : ℕ}

abbrev CompositeMatrix (m n : ℕ) := Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

theorem separableCone_zero :
    separableCone (0 : CompositeMatrix m n) := by
  refine ⟨0, (fun i => (0 : Matrix (Fin m) (Fin m) ℂ)),
    (fun i => (0 : Matrix (Fin n) (Fin n) ℂ)), ?_, ?_⟩
  · intro i
    exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.zero⟩
  · simp

theorem separableCone_add {S T : CompositeMatrix m n}
    (hS : separableCone S) (hT : separableCone T) :
    separableCone (S + T) := by
  rcases hS with ⟨k, A, B, hAB, hS⟩
  rcases hT with ⟨l, C, D, hCD, hT⟩
  let A' : Fin (k + l) → Matrix (Fin m) (Fin m) ℂ :=
    Fin.addCases A (fun j => C j)
  let B' : Fin (k + l) → Matrix (Fin n) (Fin n) ℂ :=
    Fin.addCases B (fun j => D j)
  refine ⟨k + l, A', B', ?_, ?_⟩
  · intro i
    exact Fin.addCases
      (fun j => by simpa [A', B'] using hAB j)
      (fun j => by simpa [A', B'] using hCD j) i
  · rw [hS, hT]
    simp [A', B', Fin.sum_univ_add]

theorem separableCone_smul {c : ℝ} {S : CompositeMatrix m n}
    (hc : 0 ≤ c) (hS : separableCone S) :
    separableCone (c • S) := by
  rcases hS with ⟨k, A, B, hAB, hS⟩
  refine ⟨k, (fun i => c • A i), B, ?_, ?_⟩
  · intro i
    exact ⟨(hAB i).1.smul hc, (hAB i).2⟩
  · rw [hS]
    simp_rw [Matrix.smul_kronecker]
    rw [← Finset.smul_sum]

theorem convex_separableCone :
    Convex ℝ {S : CompositeMatrix m n | separableCone S} := by
  intro S hS T hT a b ha hb hab
  have hnonneg : 0 ≤ a := ha
  have hbn : 0 ≤ b := hb
  have h₁ : separableCone (a • S) := separableCone_smul hnonneg hS
  have h₂ : separableCone (b • T) := separableCone_smul hbn hT
  have hadd := separableCone_add h₁ h₂
  simpa [hab, add_comm] using hadd

end D5.S3.Resource.EntanglementWitness
