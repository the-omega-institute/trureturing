# Golden Maximal-Order Completion

## Abstract

The Hodge lattice has a minimal golden-integer-stable completion of index two.

**Theorem 1.1 (The golden stable completion is minimal and has index two).**

$$\begin{aligned}lattice \subseteq maximalLattice \land\\\operatorname{span}\left(\mathbb{R}, maximalLattice\right) = \operatorname{top}\left(AmbientSpace\right) \land\\\forall a \in GoldenInt,\; \operatorname{map}\left(\operatorname{first}\left(a\right) id + \operatorname{second}\left(a\right) goldenOperator, maximalLattice\right) \subseteq maximalLattice \land\\\forall completed \in \operatorname{Submodule}\left(\mathbb{Z}, AmbientSpace\right),\; \left(lattice \subseteq completed \land \left(\forall a \in GoldenInt,\; \operatorname{map}\left(\operatorname{first}\left(a\right) id + \operatorname{second}\left(a\right) goldenOperator, completed\right) \subseteq completed\right)\right) \Rightarrow maximalLattice \subseteq completed \land\\\operatorname{relIndex}\left(lattice, maximalLattice\right) = 2 \land\\\operatorname{index}\left(\operatorname{range}\left(sqrtFiveOrderEmbedding\right)\right) = 2.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion.golden_maximal_order_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lattice and ambient real space are the canonical concrete objects from ExactDualLatticeFormula. The endomorphism Phi is represented by one half of the identity plus the imported integral Hodge matrix, and Wmax is the sum of the original lattice with its Phi image.

The first three clauses state literal containment, full real rank, and stability under every golden integer. A golden integer a has integral coordinates first(a) and second(a), and acts through the displayed integral linear combination of the identity and Phi.

The fourth clause quantifies over every integral submodule containing the original lattice and preserved by all of those actions. It proves that Wmax is contained in each such candidate, which is the source's minimality assertion rather than a chosen-witness encoding.

The final clauses compute two independent additive indices. The first is the relative index of the original lattice in Wmax; the second is the index of the range of the canonical ring embedding from the square-root order into GoldenInt. Both are exactly two.

Pinned Mathlib supplies the generic span, quotient, and subgroup-index infrastructure. The parity generator, concrete six-coordinate calculation, stability bridge, and both index computations are proved locally on the imported source carrier.

## References

- Truth anchor: `D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion.golden_maximal_order_completion`
- Dependency: [D5/S0/Carrier/Ring](../../../S0/Carrier/Ring.md)
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
