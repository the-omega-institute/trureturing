# Totient Periods for Two Divisor-Factorial Sequences

## Abstract

Divisor-factorial tails prove Bala's A258899 and A258903 totient-period conjectures.

The source is the COMMENTS and FORMULA fields of OEIS A258899 and A258903, which are not paginated. Both sequences have offset zero and value 1 at index zero. The modulo-7 example in the A258903 comment begins at index 1. All indices, exponents, factorials and sums here are natural numbers. Nat.div denotes natural-number division, including the factorial quotient; it is not rational division.

**Definition 1.1 (The sequence A258899).**

$$\forall n: \mathbb{N}, \operatorname{a258899}\left(n\right) = \operatorname{if} n = 0 \operatorname{then} 1 \operatorname{else} \sum_{d \in \operatorname{Nat.divisors}\left(n\right)} (2^{d} \cdot \operatorname{Nat.div}\left(\operatorname{Nat.factorial}\left(n\right), \operatorname{Nat.factorial}\left(d\right) \cdot \operatorname{Nat.factorial}\left(\operatorname{Nat.div}\left(n, d\right)\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.a258899` (`✓ std3`).

*Citation.* Paul D. Hanna; Peter Bala (2025). *OEIS A258899 and A258903: divisor-factorial sequences and totient-period conjectures*. URL: <https://oeis.org/A258899>.

*Commentary.*

OEIS A258899, FORMULA: “For n >= 1, a(n) = Sum_{d divides n} 2^d * n!/(d!*(n/d)!).” The initial value is 1, as in the entry's term list and offset. The sum ranges over Nat.divisors n.

**Definition 1.2 (The sequence A258903).**

$$\forall n: \mathbb{N}, \operatorname{a258903}\left(n\right) = \operatorname{if} n = 0 \operatorname{then} 1 \operatorname{else} \sum_{d \in \operatorname{Nat.divisors}\left(n\right)} (2^{d} \cdot 3^{\operatorname{Nat.div}\left(n, d\right)} \cdot \operatorname{Nat.div}\left(\operatorname{Nat.factorial}\left(n\right), \operatorname{Nat.factorial}\left(d\right) \cdot \operatorname{Nat.factorial}\left(\operatorname{Nat.div}\left(n, d\right)\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.a258903` (`✓ std3`).

*Citation.* Paul D. Hanna; Peter Bala (2025). *OEIS A258899 and A258903: divisor-factorial sequences and totient-period conjectures*. URL: <https://oeis.org/A258899>.

*Commentary.*

OEIS A258903, FORMULA: “For n >= 1, a(n) = Sum_{d divides n} 2^d * 3^(n/d) * n!/(d!*(n/d)!).” The initial value is 1, as in the entry's term list and offset. The sum ranges over Nat.divisors n.

**Definition 1.3 (Bala's two conjectures).**

$$(\operatorname{claim}) \Leftrightarrow ((\forall m: \mathbb{N}, (0 < m) \Rightarrow (\exists N: \mathbb{N}, \exists T: \mathbb{N}, (0 < T) \land ((T \mid \operatorname{Nat.totient}\left(m\right)) \land (\forall n: \mathbb{N}, (N \le n) \Rightarrow (\operatorname{Nat.ModEq}\left(m, \operatorname{a258899}\left(n + T\right), \operatorname{a258899}\left(n\right)\right)))))) \land (\forall m: \mathbb{N}, (0 < m) \Rightarrow (\exists N: \mathbb{N}, \exists T: \mathbb{N}, (0 < T) \land ((T \mid \operatorname{Nat.totient}\left(m\right)) \land (\forall n: \mathbb{N}, (N \le n) \Rightarrow (\operatorname{Nat.ModEq}\left(m, \operatorname{a258903}\left(n + T\right), \operatorname{a258903}\left(n\right)\right)))))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.claim` (`✓ std3`).

*Citation.* Paul D. Hanna; Peter Bala (2025). *OEIS A258899 and A258903: divisor-factorial sequences and totient-period conjectures*. URL: <https://oeis.org/A258899>.

*Commentary.*

The COMMENTS field of each entry states: “Conjecture: the sequence a(n) taken modulo a positive integer k is eventually periodic with the period dividing phi(k).” The modulus k is written m. Each conjunct has its own natural onset N and positive natural period T dividing Nat.totient m. Nat.ModEq m compares the two natural terms modulo m. Modulus 1 is included.

**Theorem 1.4 (Both totient-period assertions).**

$$(\forall m: \mathbb{N}, (0 < m) \Rightarrow (\exists N: \mathbb{N}, \exists T: \mathbb{N}, (0 < T) \land ((T \mid \operatorname{Nat.totient}\left(m\right)) \land (\forall n: \mathbb{N}, (N \le n) \Rightarrow (\operatorname{Nat.ModEq}\left(m, \operatorname{a258899}\left(n + T\right), \operatorname{a258899}\left(n\right)\right)))))) \land (\forall m: \mathbb{N}, (0 < m) \Rightarrow (\exists N: \mathbb{N}, \exists T: \mathbb{N}, (0 < T) \land ((T \mid \operatorname{Nat.totient}\left(m\right)) \land (\forall n: \mathbb{N}, (N \le n) \Rightarrow (\operatorname{Nat.ModEq}\left(m, \operatorname{a258903}\left(n + T\right), \operatorname{a258903}\left(n\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala-a258899-totient-period` (proved) by `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala-a258899-totient-period","declaration_gid":"D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; Peter Bala (2025). *OEIS A258899 and A258903: divisor-factorial sequences and totient-period conjectures*. URL: <https://oeis.org/A258899>.

*Commentary.*

For n at least 2*m+4 and a proper factorization n=d*e, the inequality 2*(d+e) <= n+4 gives d+e+m <= n. Factorial divisibility then makes m divide n!/(d!*e!). Thus only the factors 1 and n survive in the sum modulo m, giving u*v^n+v*u^n for arbitrary natural weights u,v, including zero. The theorem D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod.pow_add_totient makes both powers unchanged by a shift of Nat.totient m. Weights (2,1) and (2,3) give the two sequences. In both conjuncts N=2*m+4 and T=Nat.totient m suffice. Neither is asserted minimal.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.a258899`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.a258903`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.claim`
- Truth anchor: `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result`
- Dependency: [D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod](StirlingTransformTotientPeriod.md)
