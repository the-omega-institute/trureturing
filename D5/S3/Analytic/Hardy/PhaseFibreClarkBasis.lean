/- GID: D5/S3/Analytic/Hardy/PhaseFibreClarkBasis
   generality: G
   mirror-B: D5/B/S3/Analytic/Hardy/PhaseFibreClarkBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An orthonormal phase fibre of full finite dimension is an orthonormal basis. -/

import Mathlib.Analysis.InnerProductSpace.PiL2

/- Library-search audit trail (2026-09-04):
   * Repository and digestion searches for phase-fibre, Clark-basis, and
     full-cardinality orthonormal-family variants found no theorem covering
     this atom.
   * Pinned Mathlib provides `Orthonormal.linearIndependent`,
     `LinearIndependent.span_eq_top_of_card_eq_finrank'`, and
     `OrthonormalBasis.mk`; the proof is their thinnest composition.
   * The explicit `FiniteDimensional` assumption is required: `finrank` alone
     is zero on modules not known to be finite-dimensional, so the equality at
     `m = 0` would otherwise fail to express the source's dimension premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Hardy.PhaseFibreClarkBasis

/-- The abstract finite-dimensional step in the phase-fibre Clark-basis
theorem. Once the normalized boundary kernels form an orthonormal family and
their number equals the dimension of the model space, that family is the
underlying family of an orthonormal basis. -/
theorem phase_fibre_is_orthonormal_basis
    {𝕜 K : Type*} [RCLike 𝕜] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    (m : ℕ) (e : Fin m → K)
    (orthonormal : Orthonormal 𝕜 e)
    (dimension : Module.finrank 𝕜 K = m) :
    ∃ basis : OrthonormalBasis (Fin m) 𝕜 K, ⇑basis = e := by
  have cardEq : Fintype.card (Fin m) = Module.finrank 𝕜 K := by
    simpa using dimension.symm
  have spans : ⊤ ≤ Submodule.span 𝕜 (Set.range e) := by
    exact
      (orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank' cardEq).ge
  exact
    ⟨OrthonormalBasis.mk orthonormal spans,
      OrthonormalBasis.coe_mk orthonormal spans⟩

#print axioms phase_fibre_is_orthonormal_basis

end D5.S3.Analytic.Hardy.PhaseFibreClarkBasis
