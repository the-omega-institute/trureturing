# Lieb overlap and the weighted resolvent budget

## Abstract

The actual Petz overlap deficit pays for a weighted supported resolvent energy.

**Theorem 1.1 (The entire positive-axis budget for singular density states).**

Lean statement: `D5/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget.actual_lieb_overlap_resolvent_integral_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget.actual_lieb_overlap_resolvent_integral_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any channel Phi between finite nonempty quantum systems, density states rho and sigma with support of rho contained in support of sigma, and 0<q<1, form the actual supported relative-modular model M=(A,B,V,xi,eta). Let w(t) be (A+tI)^(-1)xi minus V(B+tI)^(-1)eta, with its Euclidean L2 norm. The function t^(q+1) norm(w(t))^2 is integrable over the entire positive axis. Its integral is at most the output overlap minus the input overlap, divided by sin(pi q)/pi. The input overlap is the real trace of rho^(1-q) sigma^q and the output overlap is the same expression for the channel images. Physical density states may be singular; no positive spectral floor is assumed for this budget. Since the energy is nonnegative and sin(pi q)/pi is positive, the output overlap is at least the input overlap: Petz-overlap monotonicity holds under the same support hypotheses.

The proof uses the original eigenvectors to identify each supported modular q-th power moment with its physical trace product. Both physical powers vanish at zero because q and 1-q are positive, so the positive-support expansions retain the physical kernels correctly. Equal spectral masses cancel the common term of order t^(q-1). The weighted resolvent gap is therefore a finite difference of genuinely integrable positive-power kernels, whose integrals are evaluated by the existing Beta/Gamma normalizer. The pointwise saturated resolvent inequality bounds t times norm(w(t))^2 by the gap; multiplication by t^q and domination give both integrability and the stated full-axis bound.

The individual raw weighted resolvent integrals diverge at infinity and are never split apart. This result supplies an energy estimate for the actual channel model, not an abstract overlap assigned by definition. It does not claim a trace-distance recovery estimate, sharpness within physical channels, or literature novelty. Fractional stability applications additionally require the appropriate cap bound and spectral floor.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget.actual_lieb_overlap_resolvent_integral_budget`
- Dependency: [D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability](EntropyDefectInverseSqrtStability.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSpectralCoordinates](../Recovery/PetzSpectralCoordinates.md)
