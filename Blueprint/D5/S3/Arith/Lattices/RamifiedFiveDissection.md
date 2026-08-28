# Ramified Five-Dissection

## Abstract

Five energy residues plus one nonzero isotropic zero-fiber state form six readouts.

**Theorem 1.1 (Five ordinary residues and one zero-fiber residual form six states).**

$$\begin{aligned}(\forall x: \operatorname{Fin}(6) \to \mathbb{Z}, \operatorname{boundaryQuadratic}(\operatorname{boundaryReduction}(\operatorname{integerReduction}(x))) = 2 \operatorname{energyResidue}(\operatorname{integerReduction}(x))) \land\\{}\operatorname{range}((x: \operatorname{Fin}(6) \to \mathbb{Z} \mapsto (\operatorname{energyResidue}(\operatorname{integerReduction}(x)), \operatorname{decide}(\operatorname{boundaryReduction}(\operatorname{integerReduction}(x)) \neq 0 \land \operatorname{boundaryQuadratic}(\operatorname{boundaryReduction}(\operatorname{integerReduction}(x))) = 0)))) = \operatorname{union}(\operatorname{range}((r: \operatorname{ZMod}(5) \mapsto (r, false))), \{(0, true)\}) \land\\{}\operatorname{ncard}(\operatorname{range}((x: \operatorname{Fin}(6) \to \mathbb{Z} \mapsto (\operatorname{energyResidue}(\operatorname{integerReduction}(x)), \operatorname{decide}(\operatorname{boundaryReduction}(\operatorname{integerReduction}(x)) \neq 0 \land \operatorname{boundaryQuadratic}(\operatorname{boundaryReduction}(\operatorname{integerReduction}(x))) = 0))))) = 6.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RamifiedFiveDissection.ramified_five_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical six-coordinate integral lattice from ExactDualLatticeFormula. Integer reduction is coordinatewise reduction into ZMod five. The boundary reduction and quadratic form are built from the explicit source matrices R-five and H; the energy uses the imported canonical Gram matrix.

The readout pairs the ordinary energy residue with the Boolean decision that the boundary vector is nonzero and isotropic. Its exact image is the five false-bit residue states together with the single zero-residue true-bit state. The final conjunct records that this concrete image has cardinality six.

The selection identity is proved from the two displayed matrices. The five ordinary states and the extra residual state are realized by explicit reduced lattice vectors; coordinatewise integer lifts then prove the same exact image on the source lattice carrier.

Repository searches found the canonical Gram data but no boundary or six-state theorem. Pinned Mathlib contributes the matrix-vector, finite range, and modular arithmetic infrastructure only.

## References

- Truth anchor: `D5/S3/Arith/Lattices/RamifiedFiveDissection.ramified_five_dissection`
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
