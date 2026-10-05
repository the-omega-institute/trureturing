# Shortfall Bound

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate shortfall bound to the stochastic ellipsoid construction.

**Theorem 1.1 (pos part le sq add).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_le_sq_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_le_sq_add` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

u⁺ ≤ u²/(4t) + t for t > 0, every real u. At u > 0 it is (u − 2t)² ≥ 0.

**Theorem 1.2 (pos part sub le sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_sub_le_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_sub_le_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(u − t)⁺ ≤ u²/(4t) for t > 0, every real u. The shifted form, with no additive t left over: it is what the drift's excess uses, where the shift is already paid for inside L.

**Theorem 1.3 (pos part shortfall le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_shortfall_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_shortfall_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shortfall splits along a pathwise lower bound. No integrability and no measurability: this is an inequality of functions.

**Theorem 1.4 (integral shortfall le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_shortfall_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_shortfall_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shortfall bound. a closes the martingale half, b the drift-excess half.

**Theorem 1.5 (integral neg part le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_neg_part_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_neg_part_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The martingale half: E[(−M)⁺] ≤ v/(4t) + t from E[M²] ≤ v alone — no mean-zero hypothesis, no tail, no Cauchy–Schwarz. At the chain v = varBound n c₃ ≈ 1.4·10⁻⁴, so t = 0.01 gives 0.0135 and t = √v/2 gives √v ≈ 0.012.

**Theorem 1.6 (integral drift excess le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_drift_excess_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_drift_excess_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The drift-excess half: E[(D − dbar)⁺] ≤ w/(4s) where dbar sits s above the centre and w bounds the centred second moment. The chain's D is κ·∑‖π_kξ_k‖², whose centre is κ·h·E[∑ rank π_k] and whose excess over κ·T·dim is bounded by the light-contact budget.

**Theorem 1.7 (shortfall le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.shortfall_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.shortfall_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hshort, assembled. L = c − (cen + s) − t, and the shortfall is v/(4t') + t' + w/(4s) with t' free. Every input is a second moment of a *centred* quantity; nothing here needs the mean of X, the lower tail of X, or Chebyshev.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_drift_excess_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_neg_part_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.integral_shortfall_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_le_sq_add`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_shortfall_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.pos_part_sub_le_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.shortfall_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar](GoodPathVar.md)
