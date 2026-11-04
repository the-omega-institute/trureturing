# Hanna's Prime-Power Correction Formula

## Abstract

Every bounded integral square-weight correction equals p minus one at p to any positive power.

The sequence a has integer values and starts at index one; a(0) is unused. All power series have rational coefficients, and every exponential and substitution is formal. IntegralSeries is the predicate from HannaLogarithmicPowerClosure: every ordinary coefficient is the image of an integer. The displayed casts are the canonical embeddings into the indicated carrier. Division in the exponent is rational field division. PowerSeries.subst takes the substituted series first and the series into which it is substituted second. The function ite selects its second argument when its first argument holds and its third argument otherwise.

**Definition 1.1 (The defining integral-series condition).**

$$\forall a: \mathbb{N} \to \mathbb{Z}, \operatorname{IsCorrection}\left(a\right) = ((\forall m: \mathbb{N}, (1 \le m) \Rightarrow ((0 \le a\left(m\right)) \land (a\left(m\right) < (m:\mathbb{Z})))) \land (\operatorname{IntegralSeries}\left(\operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{PowerSeries}.\operatorname{mk}\left((m: \mathbb{N} \mapsto \operatorname{ite}\left(m = 0, 0, \frac{(m:\mathbb{Q})^{2} - (a\left(m\right):\mathbb{Q})}{(m:\mathbb{Q})}\right))\right), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right)\right)\right)))$$

*Formalization.* `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.IsCorrection` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A384819: bounded integral square-weight corrections*. URL: <https://oeis.org/A384819>.

*Commentary.*

OEIS A384819, revision 14, NAME (no page number): "Nonnegative numbers a(n) < n for n >= 1 such that exp( Sum_{n>=1} (n^2 - a(n))*x^n/n ) is a power series with integral coefficients." The natural index m denotes the source index n. The coefficient at m=0 of the exponent is zero, and every positive coefficient is (m^2-a(m))/m. No sign condition is imposed on the exponential coefficients or Euler exponents.

**Definition 1.2 (Hanna's conjecture).**

$$\operatorname{claim}\left(\right) = (\forall a: \mathbb{N} \to \mathbb{Z}, (\operatorname{IsCorrection}\left(a\right)) \Rightarrow (\forall p: \mathbb{N}, \forall r: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((1 \le r) \Rightarrow (a\left(p^{r}\right) = (p:\mathbb{Z}) - 1))))$$

*Formalization.* `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A384819: bounded integral square-weight corrections*. URL: <https://oeis.org/A384819>.

*Commentary.*

OEIS A384819, revision 14, sole COMMENTS line (no page number): "Conjecture: a(p^n) = p - 1 when p is prime for n >= 1." The positive source exponent n is renamed r. The assertion holds for every integer sequence satisfying the defining condition, every natural prime p, including two, and every positive natural r.

**Theorem 1.3 (All positive prime powers).**

$$\forall a: \mathbb{N} \to \mathbb{Z}, (\operatorname{IsCorrection}\left(a\right)) \Rightarrow (\forall p: \mathbb{N}, \forall r: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((1 \le r) \Rightarrow (a\left(p^{r}\right) = (p:\mathbb{Z}) - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.result` (`✓ std3`). ∎

*Resolves.* `Problems/h384819-primepower` (proved) by `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"h384819-primepower","declaration_gid":"D5/S3/Arith/Congruence/HannaPrimePowerCorrection.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A384819: bounded integral square-weight corrections*. URL: <https://oeis.org/A384819>.

*Commentary.*

An integer Euler ledger gives m^2-a(m) as the sum of d times the ledger entry over positive divisors d of m. The difference between the divisor sums at successive prime powers is divisible by the larger prime power. The bound at one gives a(1)=0; at p it gives the representative p-1. For higher powers the square terms vanish modulo the larger prime power, and uniqueness of a representative in the bounded interval preserves p-1. The integer ledger theorem is integral_input_ledger in HannaDiagonalGhostPowerIntegrality. The conclusion is unbounded in p and r.

## References

- Truth anchor: `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.IsCorrection`
- Truth anchor: `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.claim`
- Truth anchor: `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](../../../S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](../../../S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.md)
