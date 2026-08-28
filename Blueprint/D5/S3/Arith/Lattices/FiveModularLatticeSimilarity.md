# Five-Modular Lattice Similarity

## Abstract

The Lambda-squared A4 lattice is five-modular under its Hodge map.

**Theorem 1.1 (The Lambda-squared A4 lattice is five-modular).**

$$\begin{aligned}dualLattice = oneFifthHodgeLattice \land\\{}\operatorname{Injective}(oneFifthHodgeMap) \land\\{}(\forall x, y: AmbientSpace, gramForm(oneFifthHodgeMap(x), oneFifthHodgeMap(y)) = \frac{1}{5} gramForm(x, y)) \land\\{}\operatorname{finrank}(\mathbb{R}, AmbientSpace) = 6 \land\\{}\operatorname{det}(integralGramMatrix) = (5:\mathbb{Z})^{3} \land\\{}\operatorname{det}(integralGramMatrix) = (5:\mathbb{Z})^{6/2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/FiveModularLatticeSimilarity.five_modular_lattice_similarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier, lattice, Gram form, dual lattice, and Hodge map are the canonical concrete objects from ExactDualLatticeFormula. In particular, the first clause reuses that family's exact equality between the dual and the image of the lattice under J divided by five.

Injectivity makes the named Hodge map an identification with its image, and the quantified Gram identity says that every pairing is scaled by one fifth. Thus lengths are scaled by one over the square root of five; this is the direct formal content of the five-modular similarity, not merely an equality of cardinalities.

The remaining public clauses record that the exact ambient carrier is six-dimensional and that the displayed integral Gram matrix has determinant both five cubed and five to the power six divided by two. Each equality is checked on the concrete imported matrix.

Repository search found the exact dual-lattice predecessor but no frozen theorem containing the similarity and determinant clauses. Pinned Mathlib supplies general bilinear and lattice infrastructure only; the finite matrix identities here are verified directly.

## References

- Truth anchor: `D5/S3/Arith/Lattices/FiveModularLatticeSimilarity.five_modular_lattice_similarity`
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
