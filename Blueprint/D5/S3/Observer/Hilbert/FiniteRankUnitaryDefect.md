# Finite Rank Unitary Defect

## Abstract

Finite-rank unitary projection defects have genuine ambient Hilbert-Schmidt energy and a quantitative finite-synthesis bound.

H is any complete complex Hilbert space, including infinite-dimensional and nonseparable spaces. S is a finite-dimensional subspace of the original H and P_S its canonical orthogonal projection. A unitary is a complex-linear isometric equivalence of H. The ambient Hilbert basis b may have an arbitrary index type beta. Define projectionDefect(S,U) = U P_S U^{-1} − P_S. Its range is finite; summability below establishes a genuine ambient Hilbert-Schmidt quantity. No finite-dimensional ambient replacement or ambient invariance assumption is used.

**Theorem 1.1 (Exact ambient square sum).**

$$\forall S\in \operatorname{Subspace}(H), \operatorname{FiniteDimensional}(S)\Rightarrow \forall c\in \operatorname{OrthonormalBasis}(iota, S), U\in \operatorname{Unitary}(H), b\in \operatorname{HilbertBasis}(beta, H), \operatorname{HasSum}(l\mapsto (\Vert \operatorname{projectionDefect}(S, U)b_{l}\Vert )^{2}, 2\sum _{i\in iota}(\Vert P_{S^{\perp}}Uc_{i}\Vert )^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect.unitary_projection_defect_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type iota is finite; beta is arbitrary. The finite-rank expansion is summed using Hilbert-basis Parseval, including uncountable bases. For two orthonormal families the overlap terms cancel, and the projection Pythagorean identity yields exactly twice the cross-block energy. The same identity on every b also identifies the square sum independently of the ambient basis.

For a pair U indexed by Fin 2, define D(S,U,b) as the square root of one half the sum over g of the ambient square sum of projectionDefect(S,U_g) on b. Thus D is exactly the root mean square of the two ambient Hilbert-Schmidt norms. Write E = EuclideanSpace(C,Fin 24), with its standard Hilbert norm.

**Theorem 1.2 (Rank twenty-four projection bridge).**

$$\forall b\in \operatorname{HilbertBasis}(beta, H), T:E\to H, (\exists z\in E, \Vert z\Vert =1\land 1\le \Vert Tz\Vert )\Rightarrow \forall U:\operatorname{Fin}(2)\to \operatorname{Unitary}(H), M:\operatorname{Fin}(2)\to \operatorname{End}(E), delta\in \mathbb{R}, 0\le delta\Rightarrow (\forall g\in \operatorname{Fin}(2), \Vert M_{g}\Vert \le 85\land \Vert U_{g}T-TM_{g}\Vert \le 95delta)\Rightarrow \exists S\in \operatorname{Subspace}(H), \operatorname{FiniteDimensional}(S)\land 1\le \operatorname{dim}(S)\le 24\land (\forall g\in \operatorname{Fin}(2), \operatorname{IsHilbertSchmidt}(\operatorname{projectionDefect}(S, U_{g})))\land (\forall g\in \operatorname{Fin}(2), \operatorname{Summable}(l\mapsto (\Vert \operatorname{projectionDefect}(S, U_{g})b_{l}\Vert )^{2}))\land \operatorname{D}(S, U, b)\le 785(delta)^{\frac{1}{24}}\land (delta=0\Rightarrow \forall g\in \operatorname{Fin}(2), \operatorname{projectionDefect}(S, U_{g})=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect.exists_rank_twentyfour_projection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All displayed maps T and M are continuous and complex-linear. The selected spectral cut has no independence, Gram-inverse or assumed-gap premise. For positive delta the cutoff is (6/5) delta^(1/24) when delta^(1/24) < 5/6. The uniform operator leakage bound and the exact ambient square sum give D <= 7(85 eta + 95 delta eta^(-23)); (6/5)^23 >= 10 yields the stated 785. For larger delta a projection contraction gives D <= 7. At delta = 0 the nonzero range of T is finite-dimensional and invariant. A unitary image has the same finite dimension, so invariance is equality and the range projection commutes with both operators. The theorem is valid for every nonnegative delta. C117FixedFourteenProjection consumes this analytic supplier with the exact twenty-four braid words, fourteen tails, polynomial parameter, residual identities and bounds 85 and 95 proved in its source-specific module. Those bounds are explicit hypotheses here and the complete original lemma is stated and proved in that consumer.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect.exists_rank_twentyfour_projection_bound`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect.unitary_projection_defect_hasSum`
- Dependency: [D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut](FiniteSynthesisSpectralCut.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](../../Quantum/Analysis/TraceClass/HilbertSchmidt.md)
