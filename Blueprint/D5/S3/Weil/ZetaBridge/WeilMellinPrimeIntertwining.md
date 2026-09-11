# Mellin Prime Intertwining

## Abstract

The actual weighted prime translations on an arithmetic Mellin model collapse to the logarithmic seed, with its full window and parity correction retained.

Write E(h)=windowMellinSum(a,M,h), Xf(x)=x*f(x), and Rf(x)=f(-x). The same half-density and factor four are used by the existing WeilPolynomialMellinWindow. The arithmetic input is Mathlib's vonMangoldt_sum. There is no alternative zeta, Gamma or Weil form.

**Definition 1.1 (Supported arithmetic synthesis).**

$$\operatorname{apply}(\operatorname{windowMellinSum}(a, M, h), x)=\operatorname{IndicatorIcc}(-a, a, \operatorname{mul}(4, \operatorname{exp}(\operatorname{div}(x, 2)), \operatorname{SumIcc}(1, M, \operatorname{apply}(h, \operatorname{mul}(n, \operatorname{exp}(x))))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.windowMellinSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a is real, M natural and h complex-valued on the reals. Closed endpoints make reflection exact. The difference from the earlier Ioc convention is isolated in the agreement theorem.

**Definition 1.2 (Actual one-sided prime block).**

$$\operatorname{primeForward}(a, M, f, x)=\operatorname{IndicatorIcc}(-a, a, \operatorname{SumIcc}(1, M, \operatorname{mul}(\operatorname{div}(\operatorname{vonMangoldt}(n), \operatorname{sqrt}(n)), \operatorname{apply}(f, x+\operatorname{log}(n)))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.primeForward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original Lambda(n)/sqrt(n) coefficients and translated function values are specified independently. All prime powers are included. The n=1 term vanishes; terms beyond exp(2a) vanish on the window, and a term exactly at that threshold affects only an endpoint.

**Definition 1.3 (Both prime translation directions).**

$$\operatorname{primeSymmetric}(a, M, f, x)=\operatorname{IndicatorIcc}(-a, a, \operatorname{SumIcc}(1, M, \operatorname{mul}(\operatorname{div}(\operatorname{vonMangoldt}(n), \operatorname{sqrt}(n)), \operatorname{add}(\operatorname{apply}(f, x+\operatorname{log}(n)), \operatorname{apply}(f, x-\operatorname{log}(n))))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.primeSymmetric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the unsigned symmetric translation block. Its negative gives the prime contribution to the canonical Weil operator. Reflection relates its two directions, but they are not identified before proof.

**Definition 1.4 (The existing polynomial seed with upper cutoff).**

$$\operatorname{cutPolynomialSeed}(a, d, A, t)=\operatorname{If}(\operatorname{LessEqual}(t, \operatorname{exp}(a)), \operatorname{SumRange}(d, \operatorname{mul}(\operatorname{apply}(A, j), \operatorname{pow}(t, \operatorname{mul}(2, j)))), 0)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.cutPolynomialSeed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seed is zero above exp(a). It is not an unknown prolate or Weil eigenfunction.

**Theorem 1.5 (Agreement with the existing canonical polynomial model).**

$$\operatorname{NotEqual}(x, -a)\Rightarrow \operatorname{windowMellinSum}(a, M, \operatorname{cutPolynomialSeed}(a, d, A), x)=\operatorname{polynomialMellinWindow}(a, M, d, A, x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.polynomial_window_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the existing mellin_monomial_polynomial_value. The cutoff m*exp(x)<=exp(a) is exactly x<=a-log(m). The half-density and every monomial agree. Only the earlier lower endpoint convention is excluded; the represented L2 functions agree.

**Theorem 1.6 (Exact all-scale arithmetic intertwining).**

$$\operatorname{And}(\operatorname{LessEqual}(\operatorname{exp}(\operatorname{mul}(2, a)), M), \operatorname{UpperSupport}(h, \operatorname{exp}(a)))\Rightarrow \operatorname{primeForward}(a, M, \operatorname{windowMellinSum}(a, M, h), x)=\operatorname{apply}(\operatorname{windowMellinSum}(a, M, \operatorname{LogTimesSeed}(h)), x)-\operatorname{mul}(x, \operatorname{apply}(\operatorname{windowMellinSum}(a, M, h), x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.prime_forward_mellin_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume exp(2a)<=M and h(t)=0 whenever t>exp(a). For every real x, the equality is B_plus E(h)=E(log(t)*h)-X E(h). Inside the window the half-density cancels sqrt(n) exactly. Terms with n*m>M vanish by support. Regroup the remaining product pairs by k=n*m and use the existing sum_{d|k} Lambda(d)=log(k). Outside the window both compressed sides vanish. No parity, positivity, regularity, spectral gap or desired residual identity is assumed.

**Theorem 1.7 (Full prime action after evenization).**

$$\operatorname{And}(\operatorname{LessEqual}(\operatorname{exp}(\operatorname{mul}(2, a)), M), \operatorname{UpperSupport}(h, \operatorname{exp}(a)))\Rightarrow \operatorname{primeSymmetric}(a, M, \operatorname{EvenPart}(\operatorname{windowMellinSum}(a, M, h)), x)=\operatorname{apply}(\operatorname{windowMellinSum}(a, M, \operatorname{LogTimesSeed}(h)), x)+\operatorname{apply}(\operatorname{windowMellinSum}(a, M, \operatorname{LogTimesSeed}(h)), -x)-\operatorname{mul}(2, x, \operatorname{apply}(\operatorname{OddPart}(\operatorname{windowMellinSum}(a, M, h)), x))-\operatorname{primeForward}(a, M, \operatorname{OddPart}(\operatorname{windowMellinSum}(a, M, h)), x)-\operatorname{primeForward}(a, M, \operatorname{OddPart}(\operatorname{windowMellinSum}(a, M, h)), -x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.prime_even_mellin_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here r=(p-Rp)/2 is the actual odd part. Finite prolate arithmetic models need not have r=0. The identity retains its coordinate and translation corrections and all complex phases. For a>=0, the paper L2 consequence bounds this correction by 2*(a+sum Lambda(n)/sqrt(n))*norm(r). This bound requires the actual L2 realization and does not claim a sufficiently small Weil residual along an unbounded scale sequence. The source analysis records the independently checked fixed-prolate parity budget. Lean elaboration, Scribe emission and the transitive axiom audit have not been run in this research continuation.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.cutPolynomialSeed`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.polynomial_window_agreement`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.primeForward`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.primeSymmetric`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.prime_even_mellin_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.prime_forward_mellin_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.windowMellinSum`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow](WeilPolynomialMellinWindow.md)
