# Singleton charge components in the periodic Rydberg ladder

## Abstract

One odd-deficit sector of the periodic ladder contains an explicitly counted family of singleton components.

The rows and columns are indexed by labelled blockade words. The restricted graph has one vertex per word of the specified charge. Distinct vertices are adjacent when the Hamiltonian entry in either direction is nonzero. PreservesCharge means that every matrix entry between unequal charges vanishes. Kills means that the matrix annihilates the basis ket and its dual row.

Hminus and Hplus sum the first and second densities printed in Eq. (46), respectively. The two agree with reversed coupling because the controlled square equals the control times the unextended square. Hladder sums the explicit plus-sign density in Eq. (71). The normalized right side of Eq. (57) uses the minus-sign base at cosine of mu, as fixed by Eq. (50).

The staggered correction uses the four cubic monomials, the two quadratic monomials and the ordered quartic monomial of Eq. (58) with their Eq. (59) coefficients. The ordered one-based pairs are (2,3), (4,5), through (L,1). Nonsingular means that the sines of v plus m and v minus m are both nonzero. The staggered conclusion uses even length and nonsingular parameters. The analytic identification with the derivative of Eq. (51) remains open and its regular domain also requires nonzero sine of mu.

**Theorem 1.1 (The common singleton family).**

$$\forall (L: \mathbb{N}), \forall (h: 12 \le L), \begin{aligned}(\operatorname{Odd}\left(L-\operatorname{targetCharge}\left(L\right)\right) \land \operatorname{card}\left(\operatorname{image}\left(\operatorname{sectorEmbedding}\left(h\right)\right)\right) = 2^{\operatorname{blocks}\left(L\right)})\\\land (\forall (d: \mathbb{C}), (\left(\operatorname{PreservesCharge}\left(\operatorname{Hminus}\left(L, d\right)\right) \land \operatorname{PreservesCharge}\left(\operatorname{Hplus}\left(L, d\right)\right)\right) \land \operatorname{PreservesCharge}\left(\operatorname{Hladder}\left(L, d\right)\right)))\\\land ((\operatorname{Even}\left(L\right)) \Rightarrow (\forall (m: \mathbb{C}), \forall (v: \mathbb{C}), (\operatorname{Nonsingular}\left(m, v\right)) \Rightarrow (\operatorname{PreservesCharge}\left(\operatorname{staggeredH}\left(L, m, v\right)\right))))\\\land (\forall (b: \operatorname{Fin}\left(\operatorname{blocks}\left(L\right)\right)\to\operatorname{Bool}), \operatorname{let} x = \operatorname{sectorEmbedding}\left(h, b\right), (\left(\left(\left(\operatorname{val}\left(x\right) = \operatorname{tiledConfig}\left(h, b\right) \land \operatorname{ket}\left(\operatorname{val}\left(x\right)\right) \ne 0\right) \land \operatorname{mulVec}\left(\operatorname{NP}\left(L\right), \operatorname{ket}\left(\operatorname{val}\left(x\right)\right)\right) = \operatorname{smul}\left(\operatorname{ofNat}\left(\operatorname{targetCharge}\left(L\right)\right), \operatorname{ket}\left(\operatorname{val}\left(x\right)\right)\right)\right) \land (\forall (d: \mathbb{C}), (\left((\operatorname{Kills}\left(\operatorname{Hminus}\left(L, d\right), \operatorname{val}\left(x\right)\right) \land \operatorname{componentSupport}\left(\operatorname{sectorSupport}\left(\operatorname{Hminus}\left(L, d\right)\right), x\right) = \operatorname{singleton}\left(x\right)) \land (\operatorname{Kills}\left(\operatorname{Hplus}\left(L, d\right), \operatorname{val}\left(x\right)\right) \land \operatorname{componentSupport}\left(\operatorname{sectorSupport}\left(\operatorname{Hplus}\left(L, d\right)\right), x\right) = \operatorname{singleton}\left(x\right))\right) \land (\operatorname{Kills}\left(\operatorname{Hladder}\left(L, d\right), \operatorname{val}\left(x\right)\right) \land \operatorname{componentSupport}\left(\operatorname{sectorSupport}\left(\operatorname{Hladder}\left(L, d\right)\right), x\right) = \operatorname{singleton}\left(x\right))))\right) \land ((\operatorname{Even}\left(L\right)) \Rightarrow (\forall (m: \mathbb{C}), \forall (v: \mathbb{C}), (\operatorname{Nonsingular}\left(m, v\right)) \Rightarrow ((\operatorname{Kills}\left(\operatorname{staggeredH}\left(L, m, v\right), \operatorname{val}\left(x\right)\right) \land \operatorname{componentSupport}\left(\operatorname{sectorSupport}\left(\operatorname{staggeredH}\left(L, m, v\right)\right), x\right) = \operatorname{singleton}\left(x\right)))))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiHamiltonians.tiled_singleton_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The embedding maps each Boolean block choice to the corresponding labelled tile word in its common charge sector. The image has exactly the displayed cardinality. The component supports are distinct singletons because the embedding is injective. Each basis ket is nonzero and has energy zero and projector charge equal to the sector label.

Each local controlled generator has zero row and column on the tile words. Both controlled pieces of the linear and squared ladder terms vanish separately. Every ordered staggered monomial also vanishes because its rightmost factor kills the ket and its leftmost factor kills its dual. The charge-preserving entries make the fixed-charge graph the support graph of the actual sector restriction.

This yields a lower bound on the number of singleton components in the specified native ladder sector. The four-representation expectation, the total component count and the largest-component asymptotics remain outside the theorem.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiHamiltonians.tiled_singleton_components`
- Dependency: [D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector](MiaoFukaiChargeSector.md)
