# Binary valuation of the even central coefficients in A402341

## Abstract

The binary digit sum gives the exact valuation of every even-indexed central coefficient.

Write a(n) for the coefficient at degree floor(15n/2) in (1 + x + ... + x^15)^n over the natural numbers. Write v_2 for the 2-adic valuation. Write s_2(m) for the sum of the base-two digits of m, with s_2(0) = 0.

**Theorem 1.1 (Exact valuation at every even index).**

$$\forall n \in \mathbb{N},\; \operatorname{Even}\left(n\right) \Rightarrow \left(0 < [x^{\lfloor \frac{15n}{2} \rfloor}](\sum_{j=0}^{15} x^{j})^{n} \land \left(v_{2}\right)\left([x^{\lfloor \frac{15n}{2} \rfloor}](\sum_{j=0}^{15} x^{j})^{n}\right) = \left(s_{2}\right)\left(\lfloor \frac{15n}{2} \rfloor\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sajid Khan Hussain (2026). *OEIS A402341, central coefficients of powers of a sixteen-term geometric polynomial*. URL: <https://oeis.org/A402341>.

*Commentary.*

At n = 0 the coefficient is 1, so its binary valuation and the digit sum are both zero. Positivity at every even n ensures that the valuation is the exponent of two in a nonzero natural number.

The geometric polynomial has an integral expression in the basis x^j(1+x)^(15-2j). For even powers the corresponding change-of-basis polynomial is a power of a square. Pairing off-diagonal products and using the binary carry inequality gives a factor of 2^(1+s_2(j)) at every positive degree j. The diagonal product gains the same factor because doubling preserves digit sum and a positive index has at least one nonzero digit.

At central degree m = 15n/2 the constant term in this basis contributes the central binomial coefficient with valuation s_2(m). Every other contribution is divisible by 2^(1+s_2(m)). The sum therefore has the valuation of its central binomial term.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation.result`
