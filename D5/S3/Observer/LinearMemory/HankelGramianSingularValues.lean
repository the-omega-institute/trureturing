/- GID: D5/S3/Observer/LinearMemory/HankelGramianSingularValues
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/HankelGramianSingularValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hankel singular values are the positive square roots of the Gramian-product spectrum. -/

import Mathlib.Analysis.InnerProductSpace.SingularValues

/- Library-search audit trail (2026-08-28):
   * Repository searches found `RobustFrameBounds`, which uses Mathlib singular
     values for a generic analysis map, but no theorem identifying a Hankel map
     with a controllability-observability Gramian product.
   * Body-shape searches for a future map composed with a self-adjoint
     controllability root found no D5 primitive to reuse.
   * Pinned Mathlib exact component hits `LinearMap.adjoint_comp`,
     `LinearMap.singularValues_fin`,
     `LinearMap.injective_iff_forall_lt_finrank_singularValues_pos`, and
     `LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff`; no exact
     whole-theorem hit was found. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.HankelGramianSingularValues

/-- If `controllabilityRoot` is the positive self-adjoint square root of the
controllability Gramian and `futureOutput` is the future-observation map, then
the spectrum of `Wc^(1/2) Wo Wc^(1/2)` gives exactly the nonzero singular
values of the past-input-to-future-output Hankel map. -/
theorem hankel_gramian_singular_values
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (controllabilityRoot : V →ₗ[K] V)
    (futureOutput : V →ₗ[K] Y)
    (rootSelfAdjoint : controllabilityRoot.adjoint = controllabilityRoot)
    (rootInjective : Function.Injective controllabilityRoot)
    (futureInjective : Function.Injective futureOutput)
    (n : ℕ) (dimension : Module.finrank K V = n) :
    let hankel := futureOutput.comp controllabilityRoot
    let gramianProduct := controllabilityRoot.comp
      ((futureOutput.adjoint.comp futureOutput).comp controllabilityRoot)
    ∃ productSymmetric : gramianProduct.IsSymmetric,
      ∀ i : Fin n,
        0 < hankel.singularValues i ∧
          hankel.singularValues i =
            Real.sqrt (productSymmetric.eigenvalues dimension i) := by
  dsimp only
  let hankel := futureOutput.comp controllabilityRoot
  let gramianProduct := controllabilityRoot.comp
    ((futureOutput.adjoint.comp futureOutput).comp controllabilityRoot)
  have gramianIdentity :
      gramianProduct = hankel.adjoint.comp hankel := by
    simp only [gramianProduct, hankel, LinearMap.adjoint_comp,
      rootSelfAdjoint, LinearMap.comp_assoc]
  let productSymmetric : gramianProduct.IsSymmetric :=
    gramianIdentity ▸ hankel.isSymmetric_adjoint_comp_self
  refine ⟨productSymmetric, fun i => ?_⟩
  have hankelInjective : Function.Injective hankel :=
    futureInjective.comp rootInjective
  have singularPositive : 0 < hankel.singularValues i := by
    rw [hankel.injective_iff_forall_lt_finrank_singularValues_pos] at hankelInjective
    apply hankelInjective i
    simpa only [dimension] using i.isLt
  refine ⟨singularPositive, ?_⟩
  have eigenvaluesAgree :
      productSymmetric.eigenvalues dimension =
        hankel.isSymmetric_adjoint_comp_self.eigenvalues dimension := by
    apply (productSymmetric.eigenvalues_eq_eigenvalues_iff dimension
      hankel.isSymmetric_adjoint_comp_self dimension).2
    exact congrArg LinearMap.charpoly gramianIdentity
  rw [hankel.singularValues_fin dimension, eigenvaluesAgree]

#print axioms hankel_gramian_singular_values

end D5.S3.Observer.LinearMemory.HankelGramianSingularValues
