# Common-band near-optimality

## Abstract

A fixed signed perturbation forces near-optimal cross energy while preserving a common variance band.

**Definition 1.1 (Three perturbation signs).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.signChoices`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.signChoices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The available perturbation coefficients form the finite set {-1,0,1}.

**Theorem 1.2 (Linearity of the price-weighted response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileResponse_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileResponse_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded measurable E and F, an integrable profile g, any exponent theta and scalar t, and x>=3, the response to E+tF equals the response to E plus t times the response to F.

**Theorem 1.3 (Quadratic expansion of cross energy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded measurable E and F, arbitrary exponents and scalar t, and X>=3, the cross energy of E+tF equals that of E, plus t times the sum of the two separately oriented mixed-response integrals, plus t^2 times the cross energy of F. No symmetry of the mixed integrals is assumed.

**Theorem 1.4 (Cancellation of the mixed terms).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_quadratic_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_quadratic_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded measurable E and F and X>=3, the cross energies of E+F and E-F, minus twice the cross energy of E, equal twice the cross energy of F.

**Theorem 1.5 (One sign on infinitely many centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_fixed_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_fixed_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two locally bounded measurable error functions and any exponent pair, there is a fixed sign in {-1,0,1} such that, on infinitely many spike centers, the absolute cross energy of E plus that sign times F is at least half the absolute cross energy of F. The sign is selected before any lower-bound constant.

**Theorem 1.6 (Preservation of a von Koch bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.vonKoch_affine_spikes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.vonKoch_affine_spikes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a<b and an admissible sparse perturbation, if E satisfies the bound O(sqrt(x)log(x)^2), then E plus any fixed real multiple of the perturbation satisfies the same bound, in the exact VonKochBoundFor predicate.

**Theorem 1.7 (Near-optimality on a common variance band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.common_band_near_optimality`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.common_band_near_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0<alpha<a<b<beta<1. Suppose E is locally bounded and measurable and its cumulative variance is asymptotic to Yu log(Y/u), uniformly for Y^alpha<=u<=Y^beta. There are an admissible starting index and a fixed sign epsilon in {-1,0,1} such that E*=E+epsilon F is locally bounded and measurable and preserves that uniform asymptotic. For every c<(b-a)^2/8, arbitrarily large real X satisfy c X^(1-b)log(X)^3/log(log(X)) <= |C(E*,X)|. For every eta>0, C(E*,X) is not O(X^(1-b)log(X)^(3-eta)). A von Koch bound for E is preserved for this same E*. Together with band_asymptotic_affine, perturbation_pointwise_bound, and vonKoch_affine_spikes, this is Theorem 492.5: both signs preserve the variance asymptotic, the perturbation has the stated pointwise bound, and both signs preserve a von Koch bound. The claim concerns the abstract variance interface; it supplies no arithmetic lower bound for psi-id.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.common_band_near_optimality`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_affine`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_fixed_sign`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileCross_quadratic_identity`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.profileResponse_affine`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.signChoices`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpness.vonKoch_affine_spikes`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport](CommonBandSharpnessTransport.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds](SparseLogSpikeBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VariancePerturbation](VariancePerturbation.md)
