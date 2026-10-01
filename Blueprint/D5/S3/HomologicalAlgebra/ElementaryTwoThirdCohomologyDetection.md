# Cyclic Detection of Actual Third Cohomology

## Abstract

All cyclic restrictions detect third cohomology of elementary two-groups with divisible-by-two coefficients.

**Theorem 1.1 (All finite ranks and all nonidentity cyclic subgroups).**

$$\forall (M: Type) [AddCommGroup M], (\forall m: M, \exists k: M, k+k=m) \Rightarrow \forall (r: \mathbb{N}) (c: H3(E(r),M)), (\forall g: E(r), g\neq1 \Rightarrow Res(g)(c)=0) \Rightarrow c=0$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be an additive commutative group with surjective doubling. For a natural number r, write E(r) = Multiplicative(Fin r to ZMod 2). Here H3(E(r),M) means Mathlib groupCohomology of Rep.trivial Z E(r) M in degree three. Res(g) is its inclusion-induced map to the cohomology of Subgroup.zpowers g, with the restricted trivial representation. Every actual class whose restrictions vanish for every nonidentity g is zero. The empty rank and rank one are included.

The proof chooses an actual cocycle representative and constructs one global two-cochain. On arbitrary unnormalized input, the cyclic invariant is f(g,g,g) + f(g,1,g). The normalizing correction is retained through a four-term product comparison. Its two mixed functions are extracted from the same cocycle and satisfy the joint equations du = 0 and 2u + dv = 0. Halving v corrects u to a two-torsion cocycle with zero diagonal. A projective section supplies its primitive, and rank induction combines all corrections into one boundary of the original cocycle.

Additive Circle has surjective doubling through the actual Circle exponential, so these coefficients give U(1) with trivial action. Checking only coordinate generators is not the premise. The result does not assert an integral homology decomposition, a classification or count of representative families, a vertex-algebra realization, or a discrete-torsion interface. No originality claim is made.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology`
