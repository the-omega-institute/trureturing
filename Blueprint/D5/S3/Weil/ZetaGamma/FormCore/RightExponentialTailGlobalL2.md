# The actual right tail has a global L2 mass bound

## Abstract

The actual right tail has a global L2 mass bound

These statements concern the literal future-tail Bochner integral R_k u(t)=integral_(s>0) exp(-k s)u(t+s). They reuse the existing kernel and translation L2 domains. They do not assert an optimal B contraction, a Gamma Fourier form domain, or positivity of the complete Weil form.

**Theorem 1.1 (A square bound with an integrable right side).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2.right_exponential_tail_sq_le_tail_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2.right_exponential_tail_sq_le_tail_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>0 and an arbitrary complex half-line L2 input u, split exp(-k s) into two equal factors. Cauchy-Schwarz gives |R_k u(t)|^2 <= k^(-1) Re(R_k(|u|^2)(t)) for every t>=0. The existing L1 tail mass formula makes the new right side globally integrable; a first moment of |u|^2 is unnecessary.

**Theorem 1.2 (Global L2 membership and a finite mass estimate).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2.right_exponential_tail_memLp_two_and_mass_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2.right_exponential_tail_memLp_two_and_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual right tail is in L2 when its measurability is supplied, and its squared L2 mass is at most k^(-2) times the input squared L2 mass. The proof retains the genuine endpoint term in the L1 mass identity and uses its nonnegativity. Measurability is an explicit premise, available from the actual unweighted L1 tail when this result is applied after exponential conjugation.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2.right_exponential_tail_memLp_two_and_mass_bound`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2.right_exponential_tail_sq_le_tail_sq`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL1Mass](RightExponentialTailL1Mass.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2](RightExponentialTailL2.md)
