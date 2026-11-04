# The labelled equal-party curve and its boundaries

## Abstract

The labelled B=C=b curve has A=N-2b and positive scalar domain 0<b<N/2. Its derivative has the sign of b-N/3, its continuous minimum is uniquely N/3, and its two scalar endpoint limits are zero. Physical sizes additionally must be positive integers.

Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0; Camargo and Nishida for the fully symmetric pure Gaussian family and equal-party observation. Size dependence here is not a dynamical evaporation theorem. The source's real scalar interpolation does not assert fractional physical modes.

**Definition 1.1 (The scalar B=C curve).**

$$F(k,N,b)=V(k,N-2b,b,b)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(k,N,b)=V(k,N-2b,b,b). For k>0 and N>0 its positive scalar domain is 0<b<N/2. For actual fixed integer total N>=3 and squeezing a>1, use k=kappa(N,a).

**Definition 1.2 (The exact derivative coefficient).**

$$D=\frac{k^2b(3b-N)[N+k(2A^2b+3Ab^2+2b^3)]}{6LRM}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curveDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put A=N-2b, M=1+k(2Nb-3b^2), L=1+2kb(N-2b), R=1+kb(N-b). The exact coefficient is k^2 b(3b-N)[N+k(2A^2 b+3Ab^2+2b^3)]/(6LRM). In the positive scalar domain every factor except 3b-N is strictly positive.

**Theorem 1.3 (Derivative and all three signs).**

$$F'(b)=D;F'(b)<0 \iff b<\frac{N}{3};F'(b)=0 \iff b=\frac{N}{3};0<F'(b) \iff \frac{N}{3}<b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>0,N>0 and 0<b<N/2, F is differentiable at b with the exact curveDerivative coefficient. Its derivative is negative if and only if b<N/3, zero if and only if b=N/3, and positive if and only if N/3<b.

**Theorem 1.4 (The unique continuous minimum).**

$$StrictAntiOn(F(k,N),(0,\frac{N}{3}]);StrictMonoOn(F(k,N),[\frac{N}{3},\frac{N}{2}));F(k,N,\frac{N}{3})\le F(k,N,b);F(k,N,b)=F(k,N,\frac{N}{3}) \iff b=\frac{N}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>0,N>0, F is strictly decreasing on (0,N/3] and strictly increasing on [N/3,N/2). At every b in (0,N/2), F(N/3)<=F(b), with equality if and only if b=N/3. The theorem proves both sides of the unique global minimum across the full scalar interval.

**Theorem 1.5 (Scalar endpoints and vacuum).**

$$F(k,N,0)=F(k,N,\frac{N}{2})=0;F(0,N,b)=0;\lim_{b\to 0^{+}}F(k,N,b)=0;\lim_{b\to (\frac{N}{2})^{-}}F(k,N,b)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve_boundaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>=0,N>0, F(k,N,0)=F(k,N,N/2)=0, with right limit zero at 0 and left limit zero at N/2. At k=0 the whole real curve is identically zero. Empty-party endpoints lie outside the three-positive-party physical theorem. No false strict vacuum derivative is asserted.

**Theorem 1.6 (The divisible-total physical curve).**

$$GM_3(N-2b,b,b,a)=F(k,N,b);GM_3(\frac{N}{3},\frac{N}{3},\frac{N}{3},a)\le GM_3(N-2b,b,b,a);GM_3(N-2b,b,b,a)=GM_3(\frac{N}{3},\frac{N}{3},\frac{N}{3},a) \iff b=\frac{N}{3};k=\kappa(N,a);b=\frac{N}{3} \iff b+b=2\frac{N}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.physical_curve_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer N>=3 divisible by 3, a>1, positive integer b with 2b<N, the actual GM3 3 (N-2b) b b a equals F(kappa(N,a),N,b). Its value is at least the actual equal-party value at (N/3,N/3,N/3), with equality if and only if b=N/3. Equivalently the multi-entropy subsystem B+C has size 2N/3. These are positive integer physical modes. For other residues the scalar continuous minimum remains valid, while no fractional-mode physical minimizer is asserted. At vacuum all admissible curve points tie by the physical vacuum theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curveDerivative`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve_boundaries`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve_derivative`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.curve_minimum`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.physical_curve_minimum`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree](ReplicaThree.md)
