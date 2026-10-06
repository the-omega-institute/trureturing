# Mid Term

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate mid term to the stochastic ellipsoid construction.

**Theorem 1.1 (mg Incr eq inner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mgIncr_eq_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mgIncr_eq_inner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Below the stopping time the stopped coefficient is the chain's own.

**Definition 1.2 (mid).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The single step the two cuts disagree on.

**Theorem 1.3 (mid eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

mid is one increment or nothing.

**Theorem 1.4 (mid sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

mid² ≤ ∑_{j<K} Δ_j² — at most one summand is non-zero.

**Theorem 1.5 (sum Vcoef eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.sum_Vcoef_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.sum_Vcoef_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∑_{j < min K (τ−1)} ⟪V_j, ξ_j⟫ = mgPart … K − mid. The telescoped sum of StoppedLowerBound.logDet_stopped_ge in terms of the martingale LogDetMartingale bounds.

**Definition 1.6 (mid Cap).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.midCap`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.midCap` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

midCap — √(∑_{j<K} Δ_j²), which dominates mid and, unlike it, is a function of a deterministic range, so every measurability and integrability fact about it comes straight from LogDetMartingale's per-increment exports. Charging midCap rather than mid to the drift side costs nothing: both have second moment at most varBound ≈ 1.4·10⁻⁴.

**Theorem 1.7 (mid le mid Cap).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_le_midCap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_le_midCap` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

mid ≤ midCap.

**Theorem 1.8 (sum Vcoef ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.sum_Vcoef_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.sum_Vcoef_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The stopped accumulation, with a measurable drift charge. mgPart … K is the deterministic martingale of LogDetMartingale; midCap is the extra drift charge.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mgIncr_eq_inner`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.midCap`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_le_midCap`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.mid_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.sum_Vcoef_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.sum_Vcoef_ge`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale](../Drift/LogDetMartingale.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound](../Walk/StoppedLowerBound.md)
