# Small-dimension physical transfer

## Abstract

Five-row APPT spectra give the complete small-dimension scalar hypotheses and physical purity bound.

**Theorem 1.1 (Necessary inequalities from one actual spectrum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical.actual_to_hyp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical.actual_to_hyp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

For n >= 5, an arbitrary ordered nonnegative spectrum whose labelled diagonal is literally APPT supplies the complete P1 Hyp whenever U = lambda_(5n-14) is positive. The normalized variables are r = V/U, H/U, D/U, q = tailEnergy/U^2 and a = headEnergy/U^2. All fields concern this same spectrum. Independent Bell assignments, star charges, subset tests and the actual variance theorem supply the necessary inequalities; no target purity or scalar hypothesis is assumed.

The tail list is monotone and nonnegative, with its first slot zero. If its largest three entries sum to at most c, its square sum is at most max(c^2, c*D/3). Writing t for the third largest entry bounds the square sum by c^2+(D-5c)*t+6*t^2 for 0 <= t <= c/3; the endpoint values are c^2 and c*D/3. With c = charge(r,H,a), this gives exactly the two tail alternatives required by P1.

**Theorem 1.2 (Full arbitrary-mass upper bound for 5 <= n <= 18).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical.physical_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical.physical_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

The square sum of every ordered nonnegative APPT spectrum is at most ((5n+8)/(5n+2)^2) times its total mass squared. If U is zero the existing homogeneous-zero theorem makes the entire spectrum zero. Otherwise actual_to_hyp supplies the normalized same-object Hyp, and FiveRowP1.scalar_bound applies for every concentrated index with real 10 <= j <= 5n-15. The original mass scales by U and the energy by U^2. The existing norm-cone concentration theorem then transfers these bounds to the original spectrum with unequal concentrated masses.

The concentration interval includes both endpoints and reduces to j = 10 at n = 5. Zero middle gaps, tied entries, zero tail entries and arbitrary total mass remain allowed. The scalar certificates and the generic physical suppliers are reused; the physical conclusion is consumed by the original FiveRowMaximumPurity.result.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical.actual_to_hyp`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical.physical_upper`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1](FiveRowP1.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical](FiveRowP2Physical.md)
