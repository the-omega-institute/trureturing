# Complete Chebyshev tail identity from absolute integrability

## Abstract

The actual complete Chebyshev tail has exact Euler normalization.

**Theorem 1.1 (Every real endpoint, with all prime powers).**

Lean statement: `D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity` (`✓ std3`). ∎

*Citation.* Jeffrey P. S. Lay (2015). *Sign changes in Mertens' first and second theorems*. URL: <https://arxiv.org/abs/1505.03589v1>.

*Commentary.*

Let K(u)=(psi(u)-u)/u^2, with Mathlib's actual Chebyshev psi. Assume K is Lebesgue integrable on (1,infinity). For every real t>=2, integral(K(u),u>t)=psi(t)/t-sum(Lambda(n)/n,0<n<=floorNat(t))+log(t)-1-EulerGamma. The sum is upper inclusive and contains all prime powers.

For real s>1, Mathlib's LSeries_eq_mul_integral_of_nonneg and the actual von Mangoldt logarithmic derivative give -Re(zeta'(s)/zeta(s))=s/(s-1)+s*integral(K(u)*u^(1-s),u>1). Chebyshev's existing linear bound supplies the partial-sum growth hypothesis; SumCoeff owns summability and the interchange. The two real integrands are separately integrable: the damped error is bounded in norm by |K| and u^(-s) is integrable.

Dominated convergence sends the damped integral to integral(K,u>1) as s tends to 1 from above. Harmonic.ZetaAsymp already proves the actual Laurent constant: the entire normalized zeta factor has value 1 and derivative EulerGamma at 1. Its continuous logarithmic derivative gives Re(zeta'/zeta)+1/(s-1) tending to EulerGamma. These limits force integral(K,u>1)=-1-EulerGamma. Residue 1 alone is never used to infer the finite part, and the totalized value zeta(1) is not substituted.

Apply the existing real-endpoint Abel summation theorem to Lambda and the reciprocal function. It gives integral(K,1..t)=sum(Lambda(n)/n,0<n<=floorNat(t))-psi(t)/t-log(t). Splitting the absolutely integrable tail at the same t proves the stated formula. No endpoint avoids integers or prime powers.

The anonymous consumer supplies the hLay argument of complete_mertens_peak from this identity. It reuses the existing Johnston-Yang integrability proof kernel_integrable on (2,infinity), exposed for this application, and extends across (1,2) where psi=0. The public frozen peak theorem and its finite kernel ledger stay unchanged. The application still assumes the all-real Johnston-Yang bound and an actual peak; it supplies neither that peak nor an unconditional Robin or RH proof.

The identity and full original anonymous 5040 consumer are kernel checked with only the permitted standard axioms. This does not discharge the Johnston-Yang bound or the actual U-peak assumption; registration and final canonical admission are separate obligations.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity`
