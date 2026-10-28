# Gibonacci Power-Window GCD Normalization

## Abstract

Integer seed content scales the gcd of all shifted power windows by its exponent.

Mbirika and Spilker's Question 6.2 concerns the gcd of infinitely many finite power sums. The seeds are arbitrary signed integers except for the pair (0,0); either individual seed may vanish. The window length is any positive natural number, and every natural exponent at least three is included.

**Definition 1.1 (The seeded integer recurrence).**

$$\forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \operatorname{gibonacci}\left(a, b\right): \mathbb{N} \to \mathbb{Z} = \operatorname{mkSol}\left(fibRecZ, [a,b]\right)$$

*Formalization.* `D5/S1/Recurrence/GibonacciPowerGcdNormalization.gibonacci` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika; Jürgen Spilker (2022). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. DOI: [10.1080/00150517.2022.12427444](https://doi.org/10.1080/00150517.2022.12427444). URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

Here fibRecZ is Mathlib's order-two linear recurrence over the integers with coefficients (1,1), and mkSol assigns its unique solution to the initial vector (a,b). Thus the sequence starts at indices zero and one, with the recurrence G(n+2)=G(n+1)+G(n).

**Definition 1.2 (The exact source window).**

$$\forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \forall k: \mathbb{N}, \forall e: \mathbb{N}, \forall t: \mathbb{N}, \operatorname{windowSum}\left(a, b, k, e, t\right) = \sum_{i = 1}^{k} \operatorname{gibonacci}\left(a, b, t + i\right)^{e}$$

*Formalization.* `D5/S1/Recurrence/GibonacciPowerGcdNormalization.windowSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika; Jürgen Spilker (2022). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. DOI: [10.1080/00150517.2022.12427444](https://doi.org/10.1080/00150517.2022.12427444). URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

The endpoints are inclusive: the terms have indices t+1 through t+k. The definition also permits k=0 and any natural exponent; the theorem uses the positive lengths and exponents at least three of the source question.

**Definition 1.3 (The nonnegative gcd of a whole integer family).**

$$\forall f: \mathbb{N} \to \mathbb{Z}, \operatorname{familyGcd}\left(f\right) = \operatorname{IntCast}\left(\operatorname{NatSetGcd}\left(\{\operatorname{natAbs}\left(\operatorname{f}\left(t\right)\right) \mid t\in\mathbb{N}\}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/GibonacciPowerGcdNormalization.familyGcd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika; Jürgen Spilker (2022). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. DOI: [10.1080/00150517.2022.12427444](https://doi.org/10.1080/00150517.2022.12427444). URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

NatSetGcd denotes Mathlib's Nat.setGcd. It is applied to the full range of natural absolute values and cast to the integers. Its universal divisibility property includes every integer divisor, including zero and negative divisors. No finite prefix or nonzero-family assumption enters this definition.

**Definition 1.4 (The infinite power-window gcd).**

$$\forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \forall k: \mathbb{N}, \forall e: \mathbb{N}, \operatorname{powerGcd}\left(a, b, k, e\right) = \operatorname{familyGcd}\left((t:\mathbb{N}) \mapsto \operatorname{windowSum}\left(a, b, k, e, t\right)\right)$$

*Formalization.* `D5/S1/Recurrence/GibonacciPowerGcdNormalization.powerGcd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika; Jürgen Spilker (2022). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. DOI: [10.1080/00150517.2022.12427444](https://doi.org/10.1080/00150517.2022.12427444). URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

This family ranges over every natural shift, starting at zero. In particular, zero-valued windows and windows of odd powers of signed terms are included.

**Theorem 1.5 (Normalization by the gcd of the seeds).**

$$\forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \left(\left(a \neq 0\right) \lor \left(b \neq 0\right)\right) \Rightarrow \left(\forall k: \mathbb{N}, \left(1 \leq k\right) \Rightarrow \left(\forall e: \mathbb{N}, \left(3 \leq e\right) \Rightarrow \left(\forall d: \mathbb{Z}, \left(d = \operatorname{IntCast}\left(\operatorname{gcd}\left(a, b\right)\right)\right) \Rightarrow \left(\left(0 < d\right) \land \left(d \cdot \operatorname{ediv}\left(a, d\right) = a\right) \land \left(d \cdot \operatorname{ediv}\left(b, d\right) = b\right) \land \left(\operatorname{gcd}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right)\right) = 1\right) \land \left(\left(\operatorname{gibonacci}\left(a, b, 0\right) = a\right) \land \left(\operatorname{gibonacci}\left(a, b, 1\right) = b\right) \land \left(\forall n: \mathbb{N}, \operatorname{gibonacci}\left(a, b, n + 2\right) = \operatorname{gibonacci}\left(a, b, n + 1\right) + \operatorname{gibonacci}\left(a, b, n\right)\right)\right) \land \left(\left(\operatorname{gibonacci}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), 0\right) = \operatorname{ediv}\left(a, d\right)\right) \land \left(\operatorname{gibonacci}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), 1\right) = \operatorname{ediv}\left(b, d\right)\right) \land \left(\forall n: \mathbb{N}, \operatorname{gibonacci}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), n + 2\right) = \operatorname{gibonacci}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), n + 1\right) + \operatorname{gibonacci}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), n\right)\right)\right) \land \left(0 \leq \operatorname{powerGcd}\left(a, b, k, e\right)\right) \land \left(0 \leq \operatorname{powerGcd}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), k, e\right)\right) \land \left(\forall r: \mathbb{Z}, \left(r \mid \operatorname{powerGcd}\left(a, b, k, e\right)\right) \iff \left(\forall t: \mathbb{N}, r \mid \operatorname{windowSum}\left(a, b, k, e, t\right)\right)\right) \land \left(\forall r: \mathbb{Z}, \left(r \mid \operatorname{powerGcd}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), k, e\right)\right) \iff \left(\forall t: \mathbb{N}, r \mid \operatorname{windowSum}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), k, e, t\right)\right)\right) \land \left(\operatorname{powerGcd}\left(a, b, k, e\right) = d^{e} \cdot \operatorname{powerGcd}\left(\operatorname{ediv}\left(a, d\right), \operatorname{ediv}\left(b, d\right), k, e\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GibonacciPowerGcdNormalization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika; Jürgen Spilker (2022). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. DOI: [10.1080/00150517.2022.12427444](https://doi.org/10.1080/00150517.2022.12427444). URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

The symbol ediv is integer division, and d is the integer cast of the natural gcd of the seeds. The reconstruction equalities prove that both quotients are exact; their gcd is one. Both recurrences, both nonnegativity assertions and both all-integer-divisor specifications are part of the conclusion. The proof uses LinearRecurrence.toInit to scale the entire seeded solution, then mul_pow and Finset.mul_sum to scale each window. Nat.dvd_setGcd_iff and Int.natAbs_dvd_natAbs characterize the infinite gcd. Divisibility antisymmetry and cancellation by the positive scalar d raised to e give the displayed equality. These are applications of general Mathlib algebra to the source question; no assertion of literature priority is made.

## References

- Truth anchor: `D5/S1/Recurrence/GibonacciPowerGcdNormalization.familyGcd`
- Truth anchor: `D5/S1/Recurrence/GibonacciPowerGcdNormalization.gibonacci`
- Truth anchor: `D5/S1/Recurrence/GibonacciPowerGcdNormalization.powerGcd`
- Truth anchor: `D5/S1/Recurrence/GibonacciPowerGcdNormalization.result`
- Truth anchor: `D5/S1/Recurrence/GibonacciPowerGcdNormalization.windowSum`
