# The actual Gaussian integral at replica order three

## Abstract

For every positive integer tripartition of the actual fully symmetric pure real Gaussian state, the integral-defined genuine multi-entropy at replica order three has an exact logarithmic formula. The spectrum and the three cut factors retain party multiplicity, including all tied party sizes and vacuum.

The scientific source is An exact balancing law for order-three Gaussian multi-entropy by Haobo Ma then Wenlin Zhang, released 4 November 2026 under CC BY 4.0. Camargo and Nishida supply the physical family and equal-party observation. The actual all-replica Fourier and positivity bridge is the prior ResidualLimit.GM3_eq_fourierGM theorem. The Gaussian integration foundation retains Mario Brcic's Apache-2.0 transplant attribution at upstream commit 254b6275b753efb609cd38ef4c85eef29b4a13b4. This order-three result does not claim the existing all-n bridge or replica-four product as new work; ReplicaFour's specialized constants and remainders concern (m,1,1).

**Definition 1.1 (The order-three parameter).**

$$kappa=\frac{3(a^2-1)}{4(N-1)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

kappa(N,a) = 3(a^2 - 1)/(4(N - 1)), three quarters of the library's squeezing parameter (a^2 - 1)/(N - 1). For physical mode counts N >= 3 and a >= 1 it is nonnegative, and for a > 1 it is positive.

**Theorem 1.2 (The integral-defined closed formula).**

$$GM_{3}=\frac{\log\frac{(1+\kappa s)^2}{D_{x}D_{y}D_{z}}}{12}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.GM3_three_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer x,y,z and real a >= 1, let N = x + y + z, s = xy + xz + yz, and D_u = 1 + kappa u(N - u). The actual GaussianMultiEntropyAsymptotic.GM3 3 x y z a equals log((1 + kappa s)^2/(D_x D_y D_z))/12. This is the real eMinus fully symmetric pure bosonic Gaussian family, with the original Lebesgue replica integrals, twists and entropy normalizations. At replica three the nine tripartite weights consist of zero, two occurrences of each labelled cut coefficient multiplied by 3/4, and two occurrences of 3s/4. The existing all-n integral/Fourier bridge and positive products justify the logarithmic reduction. All ties and permutations are in scope. Real party sizes in the scalar supplier are a scalar extension only. Replica-one continuation, higher-replica balancing, other Gaussian branches and large-N/Page asymptotics remain separate; in particular this does not take over issue 22644.

**Theorem 1.3 (Physical vacuum and squeezing).**

$$GM_{3}(x,y,z,1)=0;StrictAntiOn(a\mapsto GM_{3}(x,y,z,a),[1,\infty));\forall a>1,GM_{3}(x,y,z,a)<0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.GM3_three_behavior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer x,y,z, the actual integral-defined replica-three value is zero at a = 1, strictly decreasing on a >= 1, and strictly negative at every a > 1. The parameter kappa is strictly increasing in a on this physical ray and vanishes at vacuum. Every positive integer triple therefore ties at vacuum. No strictly negative derivative at a = 1 and no extension to fractional physical mode counts is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.GM3_three_behavior`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.GM3_three_closed`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.kappa`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar](ReplicaThreeScalar.md)
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit](ResidualLimit.md)
