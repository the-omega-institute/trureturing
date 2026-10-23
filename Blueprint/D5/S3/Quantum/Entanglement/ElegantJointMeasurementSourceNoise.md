# Physical EJM Source Noise

## Abstract

Exact Born probabilities for elegant joint measurements on independently noisy singlets.

**Theorem 1.1 (Three independent singlet visibilities give the exact equality-pattern polynomial).**

Lean statement: `D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise.ejm_noise_probability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise.ejm_noise_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nicolas Gisin (2017). *The Elegant Joint Quantum Measurement and some conjectures about N-locality in the Triangle and other Configurations*. URL: <https://arxiv.org/abs/1708.05556>.

*Commentary.*

The four tetrahedral signs have product one. The EJM vector before normalization has computational-basis entries sx+i sy, sz+1, sz-1, -sx+i sy. Each effect is its outer product scaled by 1/8. This realizes the singlet-plus-Cartesian-triplet elegant joint basis using exact complex rational matrix entries.

The EJM construction and ideal singlet-triangle distribution are due to Nicolas Gisin, Section II equation (11) and Section III equations (12)–(14) of arXiv:1708.05556v1. The source treats nonlocality as a conjecture without proof. The present Lean result verifies the explicit physical matrix model and its three-visibility noisy law.

The AB, BC and CA edges respectively use x, y and z times the singlet density matrix plus one minus that visibility times the two-qubit white state I/4. These are three independent source mixtures. The same EJM is measured at each party in cyclic outgoing/incoming wire order.

The exact physical distribution equals ejmNoiseTable for all real parameters as an algebraic identity. Nonnegative probabilities and normalization apply when all three parameters lie in [0,1], by triangle_noise_distribution. At x=y=z=1 the three equality classes have probabilities 25/256, 1/256 and 5/256 per ordered outcome.

On the diagonal visibility w, the all-equal probability is (4+9w+9w^2+3w^3)/256; an outcome with exactly two equal labels has probability (4+w-3w^2-w^3)/256; an all-distinct outcome has probability (4-3w+3w^2+w^3)/256. Off the diagonal the exactly-two-equal class depends on which source joins the equal parties. This physical identity supplies the source-noise input for triangle inflation certificates; it is not by itself a nonlocality proof.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise.ejm_noise_probability`
- Dependency: [D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise](TriangleIndependentSourceNoise.md)
