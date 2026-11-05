# Lieb overlap equality and a fixed Petz recovery

## Abstract

One fixed completed Petz channel characterizes actual overlap and entropy equality.

**Theorem 1.1 (One recovery before choosing the state or the power).**

Lean statement: `D5/S3/Quantum/Recovery/LiebOverlapPetzEquality.actual_lieb_overlap_equality_iff_fixed_petz_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LiebOverlapPetzEquality.actual_lieb_overlap_equality_iff_fixed_petz_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Fix a channel Phi between finite nonempty quantum systems and a density sigma. Choose the completed Petz channel from this pair, with its displayed full-matrix action: the usual spectral-pseudoinverse Petz core plus a reset to sigma on the orthogonal complement of the support of Phi(sigma). This one channel recovers sigma. For every rho supported by sigma and every 0<q<1, equality of the actual physical overlaps Tr(rho^(1-q) sigma^q) before and after Phi is equivalent both to equality of finite trace-log relative entropy and to recovery of rho by that same channel. The choice of recovery precedes rho and q; it is independent of both. Singular density matrices are allowed, without a spectral floor or ratio bound. Consequently, for a fixed channel and pair of states, equality at any one interior power forces equality at every interior power: each is equivalent to the same recovery equation.

The forward proof uses the full weighted resolvent-energy budget. Overlap equality forces the nonnegative integral to vanish. Since its weight is strictly positive and the resolvent error is continuous on the positive axis, the error vanishes at every positive shift. Norm saturation supplies the adjoint identity, giving zero scalar resolvent defects; the existing functional-rigidity theorem then gives the logarithmic identity and actual entropy equality. The converse applies actual overlap monotonicity to Phi and to the already fixed recovery channel. The existing fixed-reference Petz equality theorem completes both equivalences.

This is the Petz sufficiency equality mechanism for power quasi-entropies; no literature novelty, quantitative trace-distance estimate, q=0 or q=1 endpoint, or unsupported infinite-entropy equivalence is claimed. For classical source context see Hiai-Mosonyi-Petz-Beny, Quantum f-divergences and error correction, arXiv:1008.2529, Theorem 5.1. The current derivation uses the project's actual overlap budget and its existing fixed Petz channel.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LiebOverlapPetzEquality.actual_lieb_overlap_equality_iff_fixed_petz_recovery`
- Dependency: [D5/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget](../Divergence/LiebOverlapResolventIntegralBudget.md)
- Dependency: [D5/S3/Quantum/Recovery/CanonicalPetzEquality](CanonicalPetzEquality.md)
