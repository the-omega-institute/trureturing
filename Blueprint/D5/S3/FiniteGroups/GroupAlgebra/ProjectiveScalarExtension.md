# Projectivity under Coefficient Extension

## Abstract

Scalar extension from a field to a nonzero commutative algebra preserves and reflects group-algebra projectivity.

**Theorem 1.1 (Projectivity before and after scalar extension).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ProjectiveScalarExtension.projective_iff_scalarExtension`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ProjectiveScalarExtension.projective_iff_scalarExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact scope: k : Type uk is a field, R : Type uR is a nonzero commutative ring equipped with Algebra k R, G : Type uG is any group, and V : Type uV is any additive commutative group with a k-module structure. For an actual rho : Representation k G V, scalarExtension R rho is the representation on R tensor_k V with action g(r tensor v) = r tensor rho(g)(v). The conclusion is Module.Projective k[G] rho.asModule if and only if Module.Projective R[G] (scalarExtension R rho).asModule. The four universes are independent. There is no group finiteness, dimension, generation, presentation, separability, or supplied splitting hypothesis.

The action is obtained by composing rho with Mathlib's Module.End.baseChangeHom. The source reuses Representation.IntertwiningMap.equivLinearMapAsModule, Module.projective_lifting_property, Module.Projective.of_lifting_property'', Representation.finsuppLEquivFreeAsModule, LinearMap.liftBaseChange, and LinearMap.baseChange_surjective. FrobeniusCharacterDegrees.extRep already supplies the field-to-field action in the adjacent library; the present definition allows a general commutative coefficient algebra. The exact action and its projectivity equivalence were not found in the bounded library search. In particular, the named MonoidAlgebra.scalarTensorEquiv in the pinned Mathlib currently assumes CommMonoid on the indexing monoid, so it cannot simply be invoked for an arbitrary group.

For preservation, restrict the coefficient scalars of a surjection of R-representations onto the extended representation. Insert v as 1 tensor v. Projectivity of the original k[G]-module lifts this equivariant k-linear map through the restricted surjection. LinearMap.liftBaseChange then extends the lift R-linearly. The proof checks equivariance on every pure tensor and verifies that the resulting R[G]-linear map is a section. The canonical free presentation is used only to invoke the universe-polymorphic projectivity criterion.

For reflection, Mathlib's Module.Projective.exists_dual_eq_one applied to the nonzero vector 1 in the k-vector space R supplies lambda : R -> k with lambda(1) = 1. The maps i(v) = 1 tensor v and c(r tensor v) = lambda(r) v are k-linear, G-equivariant, and satisfy c composed with i = identity. Tensor any surjective k-representation map with R; the existing right-exactness theorem makes it surjective. Projectivity after extension supplies an equivariant R-linear section. Compose that section with i and c to obtain a section over k. The proof verifies contraction's naturality, which is what makes the descended composite a section. This direct lifting argument establishes the equivalence without assuming or separately building a restriction-of-projectives theorem for R[G] over k[G].

Application to cyclic-projective, globally nonprojective examples: take an existing representation rho over the prime field F_p with projective restriction to every cyclic subgroup H and with nonprojective global F_p[G]-module. Every nonzero commutative ring R of characteristic p has its canonical F_p-algebra structure. For each actual subgroup inclusion H.subtype, scalarExtension R (rho.comp H.subtype) and (scalarExtension R rho).comp H.subtype have exactly the same action: h(r tensor v) = r tensor rho(h)(v). Apply the equivalence with group H to preserve each cyclic restriction's projectivity. Apply its reflection direction with group G: a projective extended global module would force the original global module to be projective, a contradiction. Thus the same cyclic-projective/global-nonprojective pattern persists over all these coefficient rings. This is an application of the one equivalence, with no separately retained counterexample corollary.

If the input example is initially presented over a larger finite field k = F_(p^n), the theorem directly applies to rings equipped with a k-algebra structure. Characteristic p alone does not provide an embedding of that larger finite field into every R. To conclude the all-characteristic-p-rings statement from such an input one must first use an established prime-field model, or justify restriction of that model to F_p. No such extra descent for an unnamed example is asserted here. For finite-dimensional input V of dimension d over the chosen field k, a k-basis b yields the R-basis b.baseChange R of R tensor_k V via Module.Basis.baseChange, so the coefficient module remains free of rank d even when R is not a field. This is a basis statement, not an assertion of irreducibility after extension.

The argument is ordinary scalar-extension and split descent for projectivity; no minimum, unique-example, or literature novelty claim is made. The specific finite-field examples are inputs to the application explanation, not newly constructed in this module.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ProjectiveScalarExtension.projective_iff_scalarExtension`
