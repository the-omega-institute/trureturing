# Cut Variance

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate cut variance to the stochastic ellipsoid construction.

**Theorem 1.1 (good Path Cut var).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.goodPathCut_var`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.goodPathCut_var` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The stopped log determinant variance, contact failure probability and expected shortfall satisfy a joint probability budget. This ensures a path with the required determinant and contact bounds at the cut.

**Theorem 1.2 (state Triple of cut var).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.stateTriple_of_cut_var`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.stateTriple_of_cut_var` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The cut probability budget yields a positive definite terminal state with the specified determinant lower bound and controlled active contacts.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.goodPathCut_var`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.stateTriple_of_cut_var`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/FinalDischarge](../Completion/FinalDischarge.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds](../Completion/GoodPathBounds.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar](../Completion/GoodPathVar.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Theorem2R4](../Completion/Theorem2R4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated](../Drift/DriftAccumulated.md)
