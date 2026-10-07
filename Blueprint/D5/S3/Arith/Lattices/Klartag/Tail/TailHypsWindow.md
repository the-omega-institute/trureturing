# Tail Hyps Window

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail hyps window to the stochastic ellipsoid construction.

**Theorem 1.1 (hprop win).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow.hprop_win`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow.hprop_win` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The constraint process's tail at the window, named in the argument order both_sums_windowR2 reads. This is TailSideSetup3W2.tailSideHyp_latZR' at W := shellR, since windowOfR2 α p m g = (shellR α (m+1)).filter (· ∈ latZ p (m+1) g) definitionally.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow.hprop_win`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/FinalDischarge](../Completion/FinalDischarge.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup3W2](TailSideSetup3W2.md)
