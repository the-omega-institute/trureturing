# Li-Caratheodory Identity

## Abstract

The completed xi reading in the Mobius coordinate gives the normalized Li-Caratheodory expression.

**Theorem 1.1 (The completed xi reading gives the Li-Caratheodory identity).**

$$\forall z \in \mathbb{C}, \operatorname{norm}\left(z\right) < 1 \implies 0 < \operatorname{re}\left(lambdaOne\right) \implies \operatorname{liCaratheodory}\left(z\right) = \frac{1}{lambdaOne} \cdot \operatorname{logDeriv}\left(xiReading, \operatorname{mobiusCoordinate}\left(z\right)\right) \land \left(\frac{1}{2} < \operatorname{re}\left(\operatorname{mobiusCoordinate}\left(z\right)\right) \land \operatorname{liCaratheodory}\left(0\right) = 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CompletionConstants/LiCaratheodoryIdentity.li_caratheodory_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a point z in the unit disk and the sourced positive first coefficient, the declaration carries three leaves: the normalized logarithmic-derivative identity, the Mobius image's real-part inequality, and the value one at the origin.

The proof uses the completed repository xi reading, Mathlib's logarithmic-derivative composition and constant-factor rules, and the elementary real-part calculation for 1/(1-z). It makes no RH claim and introduces no replacement finite carrier.

The first leaf is the boxed formula (274.5). The second and third leaves are the substantive Mobius and normalization bullets immediately following it; the excess-connection bullet is terminological context rather than another proposition.

Counting audit: the CAS has three semantic assertions, with no proof section to exclude. The Lean proposition has two binary And nodes and three atomic leaves, in the same order as the three assertions.

Carrier audit: z and the norm-defined unit disk are carried by Complex and ‖z‖ < 1; mobiusCoordinate carries 1/(1-z); xiReading is the repository completed xi function; logDeriv carries xi'/xi; lambdaOne and liCaratheodory carry lambda_1 and C_lambda. No abstract or finite replacement carrier is introduced.

Search and provenance: repository search found the existing xiReading definition, endpoint values, differentiability, and reflection facts; Mathlib supplied logDeriv_comp, logDeriv_mul_const, Complex normSq, and inverse differentiation. The disk domain is the theorem bullet, and lambda_1 > 0 is the neighboring source equation (270.3). The declaration assumes no RH or other open conjecture.

## References

- Truth anchor: `D5/S3/Fourier/CompletionConstants/LiCaratheodoryIdentity.li_caratheodory_identity`
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](../../Zeros/Endpoints/XiEndpointValues.md)
