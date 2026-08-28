# Energy-Boundary Selection Law

## Abstract

The explicit five-adic boundary map preserves twice the six-dimensional lattice energy modulo five.

**Theorem 1.1 (Boundary quadratic value equals twice the lattice energy modulo five).**

$$\forall x: \operatorname{Fin}(6) \to \mathbb{Z}, \operatorname{boundaryQuadraticForm}(\operatorname{boundaryMap}(x)) = 2 \operatorname{latticeEnergyModFive}(x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw.energy_boundary_selection_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variable x ranges over the integral coordinate vectors in the chosen six-element basis of Lambda^2 A4. The imported lattice family owns this coordinate index and the displayed integral Gram matrix.

The boundary map multiplies the reduction of x modulo five by the source three-by-six matrix R_5. The boundary quadratic form uses the source three-by-three symmetric matrix H, while the lattice energy uses the imported Gram matrix G.

Direct exact matrix normalization over ZMod 5 proves that the boundary quadratic value is twice the reduced Gram energy for every integral lattice coordinate vector.

## References

- Truth anchor: `D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw.energy_boundary_selection_law`
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
