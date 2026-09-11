/- GID: D5/S3/Quantum/Matrix/RecordSymmetryNoGo
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/RecordSymmetryNoGo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equivariant self-adjoint idempotents in an irreducible matrix representation are
   only zero or identity; nontrivial equivariant orthogonal records force reducibility. -/

import D5.S3.Quantum.Matrix.CrossSpeciesConsensus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Matrix.RecordSymmetryNoGo

open D5.S3.Quantum.Matrix.CrossSpeciesConsensus

variable {G n : Type*} [Group G] [Fintype n] [DecidableEq n]

private theorem scalar_idempotent_binary (r : ℝ) (h : (r : ℂ) * r = r) :
    r = 0 ∨ r = 1 := by
  have h' : r * r = r := by
    exact_mod_cast h
  have hfactor : r * (r - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hr | hr
  · exact Or.inl hr
  · exact Or.inr (sub_eq_zero.mp hr)

/-- In an irreducible representation, an equivariant Hermitian idempotent is trivial. -/
theorem equivariant_selfAdjoint_idempotent_eq_zero_or_one
    (U : G →* Matrix n n ℂ)
    (h_irreducible : Representation.IsIrreducible (matrixRepresentation U))
    (P : Matrix n n ℂ) (h_selfAdjoint : P.IsHermitian)
    (h_idempotent : P * P = P)
    (h_equivariant : ∀ g : G, P * U g = U g * P) :
    P = 0 ∨ P = 1 := by
  obtain ⟨r, hP⟩ := equivariant_selfAdjoint_eq_smul_id_of_irreducible
    U h_irreducible P h_selfAdjoint h_equivariant
  rcases isEmpty_or_nonempty n with h_empty | h_nonempty
  · exact Or.inl (Subsingleton.elim _ _)
  · obtain ⟨i⟩ := h_nonempty
    have hscalar : (r : ℂ) * r = r := by
      have hmatrix : (r : ℂ) • ((r : ℂ) • (1 : Matrix n n ℂ)) = (r : ℂ) • 1 := by
        simpa [hP] using h_idempotent
      have hentry := congrArg (fun M : Matrix n n ℂ => M i i) hmatrix
      simpa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] using hentry
    rcases scalar_idempotent_binary r hscalar with hr | hr
    · exact Or.inl (by simpa [hP, hr])
    · exact Or.inr (by simpa [hP, hr])

/-- A nonzero proper equivariant Hermitian idempotent witnesses reducibility. -/
theorem nontrivial_equivariant_selfAdjoint_idempotent_implies_reducible
    (U : G →* Matrix n n ℂ)
    (P : Matrix n n ℂ) (h_selfAdjoint : P.IsHermitian)
    (h_idempotent : P * P = P)
    (h_equivariant : ∀ g : G, P * U g = U g * P)
    (h_nonzero : P ≠ 0) (h_not_one : P ≠ 1) :
    ¬ Representation.IsIrreducible (matrixRepresentation U) := by
  intro h_irreducible
  rcases equivariant_selfAdjoint_idempotent_eq_zero_or_one U h_irreducible P
      h_selfAdjoint h_idempotent h_equivariant with h0 | h1
  · exact h_nonzero h0
  · exact h_not_one h1

/-- Two nonzero orthogonal equivariant records cannot occur under one irreducible symmetry. -/
theorem two_nonzero_orthogonal_equivariant_records_imply_reducible
    (U : G →* Matrix n n ℂ)
    (P Q : Matrix n n ℂ)
    (hP_selfAdjoint : P.IsHermitian) (hQ_selfAdjoint : Q.IsHermitian)
    (hP_idempotent : P * P = P) (hQ_idempotent : Q * Q = Q)
    (hP_equivariant : ∀ g : G, P * U g = U g * P)
    (hQ_equivariant : ∀ g : G, Q * U g = U g * Q)
    (hP_nonzero : P ≠ 0) (hQ_nonzero : Q ≠ 0)
    (h_orthogonal : P * Q = 0) :
    ¬ Representation.IsIrreducible (matrixRepresentation U) := by
  intro h_irreducible
  rcases equivariant_selfAdjoint_idempotent_eq_zero_or_one U h_irreducible P
      hP_selfAdjoint hP_idempotent hP_equivariant with hP0 | hP1
  · exact hP_nonzero hP0
  · have hQ0 : Q = 0 := by simpa [hP1] using h_orthogonal
    exact hQ_nonzero hQ0

end D5.S3.Quantum.Matrix.RecordSymmetryNoGo
