# Zero-Hilbert Cayley Unitarity

## Abstract

The Cayley multiplier on the multiplicity-expanded zero Hilbert space has the exact star-unitarity defect, and its vanishing is equivalent to the Riemann hypothesis.

**Theorem 1.1 (The Cayley defect and all of its unitarity characterizations).**

$$\begin{gathered}\forall Z: \operatorname{ZeroData},\\{}\forall h: (\forall \rho \in \mathbb{C}, (((\operatorname{riemannZeta}\left(\rho\right) = 0) \land (\neg \exists n \in \mathbb{N}, \rho = -2(n+1))) \land (\rho \neq 1)) \Rightarrow (\exists n \in \mathbb{N}, \operatorname{zero}\left(Z, n\right) = \rho)),\\{}(\forall v \in \operatorname{ZeroCoordinate}\left(Z\right), \operatorname{let} \delta_{v} = \left\lVert \operatorname{cayleyCoefficient}\left(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right)\right) \right\rVert^{2}-1;\\{}((((\operatorname{zeroCayleyOperator}\left(Z\right)(\operatorname{single}\left(2, v, 1\right)) = \operatorname{cayleyCoefficient}\left(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right)\right)\cdot\operatorname{single}\left(2, v, 1\right)) \land ((\operatorname{zeroCayleyOperator}\left(Z\right)^{*}\operatorname{zeroCayleyOperator}\left(Z\right)-I)(\operatorname{single}\left(2, v, 1\right)) = \delta_{v}\cdot\operatorname{single}\left(2, v, 1\right))) \land (\delta_{v} = \frac{1-2\Re(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right))}{\left\lVert \operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right) \right\rVert^{2}})) \land ((\left\lVert \operatorname{cayleyCoefficient}\left(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right)\right) \right\rVert = 1) \iff (\Re(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right)) = \frac{1}{2}))) \land ((\Re(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right)) = \frac{1}{2}) \iff (\left\lVert \operatorname{zeroCayleyOperator}\left(Z\right)(\operatorname{single}\left(2, v, 1\right)) \right\rVert = \left\lVert \operatorname{single}\left(2, v, 1\right) \right\rVert))) \land\\{}((\operatorname{RiemannHypothesis}) \iff (\forall v \in \operatorname{ZeroCoordinate}\left(Z\right), \left\lVert \operatorname{cayleyCoefficient}\left(\operatorname{zero}\left(Z, \operatorname{fst}\left(v\right)\right)\right) \right\rVert = 1)) \land\\{}((\operatorname{RiemannHypothesis}) \iff (\operatorname{zeroCayleyOperator}\left(Z\right)^{*}\operatorname{zeroCayleyOperator}\left(Z\right) = I)) \land\\{}((\operatorname{RiemannHypothesis}) \iff (\operatorname{Unitary}\left(\operatorname{zeroCayleyOperator}\left(Z\right)\right))) \land\\{}((\forall v \in \operatorname{ZeroCoordinate}\left(Z\right), \left\lVert \operatorname{zeroCayleyOperator}\left(Z\right)(\operatorname{single}\left(2, v, 1\right)) \right\rVert = \left\lVert \operatorname{single}\left(2, v, 1\right) \right\rVert) \iff (\operatorname{Unitary}\left(\operatorname{zeroCayleyOperator}\left(Z\right)\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity.cayley_unitarity_defect_formula_on_zero_hilbert_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I_Z be the dependent sum of Fin(multiplicity(n)) over the distinct zeros stored by Z, and let H_Z be ell squared on I_Z. The vector e_v is the canonical single-coordinate vector. The coefficient c_v is (Z.zero(v.1) - 1) / Z.zero(v.1), and C_Z is the repository's bounded diagonal operator built from the full coefficient family.

The exhaustiveness binder states that Z covers every zeta zero in the domain quantified by Mathlib's RiemannHypothesis. This is the public bridge from the source's multiset of all nontrivial zeros to ZeroData, whose native exhaustive field covers zeros in the open strip.

For every multiplicity coordinate, the statement gives the diagonal action, the basis-vector star defect, both scalar formulas for the defect, and the two pointwise norm characterizations. It then identifies the Riemann hypothesis with coefficient norm one, the Gram identity, and standard unitary membership, and directly relates the latter to norm preservation on every canonical basis vector.

Boundedness follows from continuity and nonvanishing of zeta near zero, which gives a uniform lower bound for the norms of all supplied zeros. The result is conditional on supplied ZeroData and its explicit exhaustiveness bridge; it does not construct either object or prove the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity.cayley_unitarity_defect_formula_on_zero_hilbert_space`
- Dependency: [D5/S3/Midline/Cayley/CayleyUnitarityDefect](CayleyUnitarityDefect.md)
- Dependency: [D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization](../../Observer/Approximation/ReadoutUpdateCommutatorFactorization.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](../../Weil/ZetaBridge/RhLocatesZeroData.md)
