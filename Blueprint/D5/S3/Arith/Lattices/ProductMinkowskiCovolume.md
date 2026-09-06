# Product Minkowski Covolume

## Abstract

Finite product fundamental domains yield the discriminant covolume in every finite power.

**Theorem 1.1 (Dependent finite products of basis fundamental domains).**

$$\operatorname{finite}\left(I\right), \operatorname{realNormedSpaces}\left(E\right), \operatorname{bases}\left(b, J, E\right) \Rightarrow \operatorname{FD}\left(\operatorname{PiBasis}\left(b\right)\right) = \operatorname{SetPi}\left(I, \operatorname{FD}\left(b_{i}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ProductMinkowskiCovolume.fundamentalDomain_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite type I and families of types J(i) and E(i), assume each E(i) is a normed additive commutative group and a real normed space, and let b(i) be a J(i)-indexed real basis of E(i). No finiteness of J(i) is assumed. FD denotes ZSpan.fundamentalDomain. The sigma-indexed Pi basis has exactly the component coordinate inequalities.

**Theorem 1.2 (Product volume for sigma-finite component measures).**

$$\operatorname{finite}\left(I\right), \operatorname{realNormedSpaces}\left(E\right), \operatorname{bases}\left(b, J, E\right), \operatorname{sigmaFiniteVolumes}\left(E\right) \Rightarrow \operatorname{vol}\left(\operatorname{FD}\left(\operatorname{PiBasis}\left(b\right)\right)\right) = \prod_{i\in I} \operatorname{vol}\left(\operatorname{FD}\left(b_{i}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ProductMinkowskiCovolume.volume_fundamentalDomain_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume all the hypotheses of the factorization theorem. In addition, each E(i) has a MeasureSpace whose volume is sigma-finite. The volume on the dependent function space is the canonical product measure. The equality is in the extended nonnegative reals and requires no Haar or Borel hypothesis.

**Theorem 1.3 (Discriminant covolume of the finite-power Minkowski lattice).**

$$\operatorname{NumberField}\left(K\right), r \in \mathbb{N} \Rightarrow \operatorname{covol}\left(\operatorname{restrictedMinkowskiLattice}\left(K, r\right)\right) = {{2^{-1}}^{\operatorname{c}\left(K\right)} \times \sqrt{\operatorname{abs}\left(\operatorname{disc}\left(K\right)\right)}}^{r}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ProductMinkowskiCovolume.restrictedMinkowskiLattice_covolume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field with a NumberField instance and let r be any natural number, including zero. The lattice is the existing restrictedMinkowskiLattice K r, with canonical product volume on Fin(r) to mixedSpace(K). The symbol c(K) denotes NumberField.InfinitePlace.nrComplexPlaces K and disc(K) denotes NumberField.discr K cast to the reals. The formula follows by applying the new product factorization to Mathlib's one-copy discriminant formula.

## References

- Truth anchor: `D5/S3/Arith/Lattices/ProductMinkowskiCovolume.fundamentalDomain_pi`
- Truth anchor: `D5/S3/Arith/Lattices/ProductMinkowskiCovolume.restrictedMinkowskiLattice_covolume`
- Truth anchor: `D5/S3/Arith/Lattices/ProductMinkowskiCovolume.volume_fundamentalDomain_pi`
- Dependency: [D5/S3/Arith/Lattices/RestrictedScalarFreeMinkowskiLattice](RestrictedScalarFreeMinkowskiLattice.md)
