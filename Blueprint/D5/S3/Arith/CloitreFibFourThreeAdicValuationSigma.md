# Cloitre's Fibonacci Three-Adic Valuation and Divisor Sum

## Abstract

The highest power of three dividing F(4n) satisfies the Marcus and Bala formulas.

All variables and values lie in the natural numbers N, and n is the index. F denotes Nat.fib, v_3 denotes padicValNat 3, and sigma_1 (also written sigma) denotes ArithmeticFunction.sigma 1, the sum of positive divisors. The function a is A074724 as defined below. Powers and products are natural-number operations; each displayed subtraction is truncated natural-number subtraction.

**Definition 1.1 (The power of three in F(4n)).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = 3^{\left(\operatorname{v}_{3}\right)\left(\operatorname{F}\left(4 \cdot n\right)\right)}$$

*Formalization.* `D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.a` (`✓ std3`).

*Citation.* Benoit Cloitre; Michel Marcus; Peter Bala (2022). *OEIS A074724, highest power of 3 dividing F(4n), with the Marcus and Bala conjectures*. URL: <https://oeis.org/A074724>.

*Commentary.*

The exponent is the 3-adic valuation of F(4n). For a positive index, this defines the highest power of three dividing that Fibonacci number. At zero, the total Lean definition uses padicValNat 3 0 = 0 and therefore gives a(0) = 1; the theorem below concerns positive indices.

**Theorem 1.2 (The valuation and divisor-sum formulas).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{a}\left(n\right) = 3^{(\left(\operatorname{v}_{3}\right)\left(n\right) + 1)}) \land (\operatorname{a}\left(n\right) \cdot (\left(\operatorname{\sigma}_{1}\right)\left(3 \cdot n\right) - 3 \cdot \left(\operatorname{\sigma}_{1}\right)\left(n\right)) = \left(\operatorname{\sigma}_{1}\right)\left(3 \cdot n\right) - \left(\operatorname{\sigma}_{1}\right)\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a074724-cloitre-fib-four-three-adic-valuation-sigma` (proved) by `D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a074724-cloitre-fib-four-three-adic-valuation-sigma","declaration_gid":"D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.result","resolution_kind":"proved"} -->

*Citation.* Benoit Cloitre; Michel Marcus; Peter Bala (2022). *OEIS A074724, highest power of 3 dividing F(4n), with the Marcus and Bala conjectures*. URL: <https://oeis.org/A074724>.

*Commentary.*

For n > 0, A051064(n) = v_3(3n) = v_3(n) + 1. The valuation formula follows from the rank-12 criterion for divisibility of F(k) by nine and induction using the Fibonacci tripling identity. Bala's formula is stated with the denominator multiplied out in N. Writing n = 3^e m with 3 not dividing m gives sigma_1(3n) - 3 sigma_1(n) = sigma_1(m) > 0; positivity of the denominator is proved inside. The separate remark 'Equivalently, a(n) = A088838(n) - A074724(n)' is not part of the settled claim.

## References

- Truth anchor: `D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.a`
- Truth anchor: `D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma.result`
