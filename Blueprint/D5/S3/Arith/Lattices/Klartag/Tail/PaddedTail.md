# Padded Tail

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate padded tail to the stochastic ellipsoid construction.

**Definition 1.1 (Phi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.Phi`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.Phi` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Φ(r) = min(1/2, e^{−r²/2}/(√(2π)·r)), Klartag eq. (48).

**Theorem 1.2 (integral Ioi mul exp neg sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.integral_Ioi_mul_exp_neg_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.integral_Ioi_mul_exp_neg_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

x ↦ x·e^{−x²/2} integrates to e^{−a²/2} over (a, ∞).

**Theorem 1.3 (integrable On exp neg sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.integrableOn_exp_neg_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.integrableOn_exp_neg_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

e^{−x²/2} is integrable on any (r, ∞).

**Theorem 1.4 (gaussian tail le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussian_tail_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussian_tail_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For positive r, the Gaussian tail integral is at most exp(-r^2/2)/r. On the half-line beyond r, bounding one by x/r reduces the estimate to an exactly integrable derivative.

**Theorem 1.5 (gaussian Real Ici le tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_tail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

P(Z ≥ r) ≤ e^{−r²/2}/(√(2π)·r) for a standard Gaussian Z and r > 0.

**Theorem 1.6 (gaussian Real Ici zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

P(Z ≥ 0) = 1/2 for a standard Gaussian, by symmetry.

**Theorem 1.7 (gaussian Real Ici le Phi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_Phi`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_Phi` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

P(Z ≥ r) ≤ Φ(r) for a standard Gaussian and r > 0 — Klartag eq. (49).

**Theorem 1.8 (gaussian Real Ici le Phi var).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_Phi_var`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_Phi_var` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The same bound for a centred Gaussian of variance σ²: P(Z ≥ a) ≤ Φ(a/σ).

**Theorem 1.9 (padded increment tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.padded_increment_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.padded_increment_tail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The padded-increment tail (Prop 4.1, discrete form). hit is the event {∃ k ≤ N, M_k ≤ 0} (the lattice point x becomes a contact point by time T); lev is the event {min_{k ≤ N} S̃_k ≤ −M₀} for the *padded* walk S̃, whose increments are i.i.d. N(0, δ) with δ = h·|x|⁴; S is the terminal value S̃_N, whose law is N(0, T·q²) with q = |x|² (because N·δ = T·|x|⁴). The two supplied inequalities are the two places the discrete argument replaces continuous time: * hsym — conditional symmetry of the padding at the first passage time, replacing Dambis-Dubins-Schwartz (factor 2); * hlevy — Lévy's maximal inequality for i.i.d. symmetric increments, replacing the reflection principle (factor 2). The conclusion carries the constant 4 against the paper's 2: the discretisation costs exactly one factor of 2, which moves only the universal constant c of Theorem 1.2 and not the n² (the n² is fixed by n²T/4 = 4 log n against e^{n²T/8} = n², and a constant in front of K_t(L) is absorbed by ∫₀^T e^{n²t/8} dt ≤ (8/n²)·e^{n²T/8}).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.Phi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_Phi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_Phi_var`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_le_tail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussianReal_Ici_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.gaussian_tail_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.integrableOn_exp_neg_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.integral_Ioi_mul_exp_neg_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.padded_increment_tail`
