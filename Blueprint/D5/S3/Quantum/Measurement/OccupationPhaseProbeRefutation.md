# Joint occupation defeats linear phase probes

## Abstract

A bound on all linear occupation phases need not bound every phase of a constrained activity law.

**Definition 1.1 (The probe sufficiency assertion).**

$$claim \iff ((\forall c: \operatorname{Fin}(5) \to \mathbb{R}, \frac{\operatorname{V}(\operatorname{L}(c))}{10} \le \operatorname{E}(\operatorname{L}(c))) \Rightarrow (\forall f: \mathbb{N} \to \mathbb{R}, \frac{\operatorname{V}(f)}{10} \le \operatorname{E}(f)))$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier contains all five-site binary words without adjacent occupied sites. Site one is the least significant bit. The activities are (100,1,100,1,100), the partition function is 1030504, and p(s) is the product of the occupied-site activities divided by this partition function.

The normalized site weights are (368/2565,5101/17955,289/1995,5101/17955,368/2565). V(f) is sum_s p(s) f(s)^2 minus (sum_s p(s) f(s))^2. For zero-based bit positions i=0,...,4, E(f) sums p(s) w_i lambda_i/(1+lambda_i) times (f(s)-f(s+2^i))^2 over empty sites whose insertion stays in the same carrier. Every undirected edge is counted once from its empty endpoint.

L(c)(s) is the sum of c_i s_i. All coefficients are real. The assertion extends a lower bound valid on every linear occupation function to every real phase function. Functions are defined on natural words, but their values outside the carrier do not enter either form.

**Theorem 1.2 (The lower bound does not extend).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every linear occupation function, E(L(c))-V(L(c))/10 is a sum of fifteen squares with positive coefficients, divided by 962888835832892640. The five single-variable coefficients are 296233677576200,201992930717100,197414496485100,201992930717100,296233677576200, with the second and fourth variables scaled by 1/10. The remaining ten squares correspond to pairs of distinct occupation coefficients.

The nonlinear function f(s)=(1-s_1)(1-s_3)+s_2 includes the joint occupation s_1 s_3. It has E(f)=8757839/207641403480 and V(f)=131365851/265484623504. Its quotient is 132720413542/1557033067485, strictly below 1/10, so it contradicts the asserted extension.

The two forms use the same positive law and the same legal insertion edges. The conclusion concerns the sufficiency of linear occupation probes. It makes no claim about a physical energy, experimental implementation, or failure of the separate comparison between the two spectral edges.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.result`
