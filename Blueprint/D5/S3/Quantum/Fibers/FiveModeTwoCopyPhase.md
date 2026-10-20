# Five-Mode Two-Copy Phase Magnitude

## Abstract

A real joint rank-one effect on two copies detects the squared hidden phase magnitude.

Use the five-coordinate phase mixture from FiveModePhaseLift. On two copies, the ray supported at (2,2) and (4,4) with coefficients 1 and -1 defines bellEffect. For q in the real closed unit interval, twoCopyProbability(q) is the real part of the trace of this effect against the Kronecker square of mixture(q).

**Theorem 1.1 (Two-copy Bell readout).**

$$\forall q\in \operatorname{IccReal}(0,1),\operatorname{PSD}(bellEffect)\land \operatorname{Tr}(bellEffect)=1\land bellEffect \cdot bellEffect=bellEffect\land \operatorname{twoCopyProbability}(q)=\frac{1+{1-2q}^{2}}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase.two_copy_bell_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized real Bell effect is positive, trace one, and idempotent. Its two-copy probability on the phase mixture is exactly (1 + (1 - 2q)^2) / 4. The readout distinguishes the balanced mixture from the endpoints but is invariant under q ↦ 1-q.

This is a finite-dimensional operational result. It supplies no Source, kappa, p4, rho44, or rho24 bridge, no physical preparation, and no QFT realization.

For the same-family comparison, the input at q is two independent copies mixture(q) ⊗ mixture(q), and the input at r is mixture(r) ⊗ mixture(r). Write B(q) for the single specified Bell effect's value twoCopyProbability(q). For q and r in the real closed unit interval, the complete observational fiber of this readout is:

$$
\forall q\in \operatorname{IccReal}(0,1), \forall r\in \operatorname{IccReal}(0,1), (\operatorname{twoCopyProbability}(q) = \operatorname{twoCopyProbability}(r)) \iff (q=r) \lor (q+r=1)
$$

To derive it, assume B(q) = B(r) and substitute the existing two_copy_bell_readout equality at q and r. Cancelling the common affine map x ↦ (1 + x) / 4 gives equality of the squares (1 - 2q)^2 and (1 - 2r)^2. The pinned Mathlib lemma sq_eq_sq_iff_eq_or_eq_neg then gives either 1 - 2q = 1 - 2r or 1 - 2q = -(1 - 2r); normalizing these affine equalities yields q = r or q + r = 1. Conversely, either normalized equality makes the two squares, and hence B, equal. At q = 1/2 the two alternatives coincide, so its fiber is a singleton; elsewhere the fiber is the pair {q, 1 - q}.

This fiber describes this one fixed real Bell readout and the same-family preparation parameter. It does not classify all two-copy protocols, adaptive measurements, other joint effects, or arbitrary post-processing. The native Source, kappa, density/QFT, and preparation bridges remain absent, so the result does not assert a physical realization of the modeled mixtures.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase.two_copy_bell_readout`
- Dependency: [D5/S3/Quantum/Fibers/FiveModePhaseLift](FiveModePhaseLift.md)
