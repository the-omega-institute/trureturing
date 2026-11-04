# Original full-kernel certificate source

## Abstract

The complete actual-K moment certificate.

**Theorem 1.1 (Finite Gamma head below the complete mixture).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_head_gamma`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_head_gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D>0, q>=1, m>=1 and delta_q<=1/m, the first M terms give Re Q_P >= E sum_{n<M} c_n 2lambda_n/(1+lambda_n^2/m), with the literal positive mixture coefficients and rates. Each term consumes the division-free Gamma gap certificate; positive energy permits cancellation inside that branch, while E=0 follows from the nonnegative exponential form. The existing complete-tail theorem keeps every omitted term nonnegative. The small-window endpoints consume M=20 with m=138 and m=1600.

**Theorem 1.2 (complete positive mixture logarithmic).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_logarithmic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_logarithmic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete actual P(t)=exp(-abs(t)/2)trivialT(abs(t)) has Re Q_P >= (log(q/D)-1)E for q>=1, q/D>=8 and atomic moments 0,...,q zero. The retained compiled exponential-moment supplier is consumed at every actual rate 2k+1/2. Absolute coefficient domination justifies quadratic interchange, and every tail form is nonnegative. For M=floor(q/D), A_M=H_(2M+1)-1 and the exact loss is delta_q(2M^2+3M+A_M/4). Harmonic and log/floor bounds give the coefficient without dividing by E.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_head_gamma`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_logarithmic`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic](ActualKernelMomentArithmetic.md)
