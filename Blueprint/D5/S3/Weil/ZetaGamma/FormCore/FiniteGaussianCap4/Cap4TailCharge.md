# Complete infinite tail charge control

## Abstract

Complete infinite tail charge control

**Theorem 1.1 (The whole reciprocal-energy tail).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.complete_tail_reciprocal_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.complete_tail_reciprocal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let w(0)=1 and w(k+1)=w(k)*(k+9/4)*(k+1/2)/((k+11/4)*(k+1)). Set H(k)=((2*k+9/4)^2-440)/10-3/4. The entire series over k>=16 of w(k)/H(k) is summable and at most S=1028725771676171625/157438844598004744192.

The proof constructs a positive telescoping potential w(k)*(1+(k+9/4)/2)/H(k). Its one-step debit dominates w(k)/H(k) for every k>=16, using an explicit shifted cubic with positive coefficients. Finite prefixes retain their final nonnegative potential before passing to the infinite sum.

**Theorem 1.2 (Energy summability proves charge convergence).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.complete_tail_charge_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.complete_tail_charge_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence u indexed from zero, assume only summability of H(16+n)*w(16+n)*u(n)^2. Then w(16+n)*u(n) is summable and rho*(sum_n w(16+n)*u(n))^2 is at most sum_n H(16+n)*w(16+n)*u(n)^2, where rho=1/S. The index n=0 corresponds to mode 16.

The preceding reciprocal-tail estimate supplies the new analytic input to finite Cauchy-Schwarz bounds and their limit. Charge convergence is proved from energy summability. This sequence theorem assumes no physical Gaussian expansion and establishes no final spectral quotient or RH statement. The estimates are repository-derived; standard summability and Cauchy-Schwarz theorems are reused.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.complete_tail_charge_bound`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge.complete_tail_reciprocal_bound`
