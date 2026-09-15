# Bala's Cubic Three-Adic Congruence

## Abstract

Bala's cubic recurrence satisfies the conjectured power-of-three congruence.

The sequence a maps the natural numbers to the integers; n and r are natural indices. The symbol ∣ denotes divisibility in ℤ, so the modulus and the sequence difference are integers. Powers have natural exponents. Only the Conjecture line in Peter Bala's Nov 15 2022 block for A002000 is settled here, for every n and every r<=n. The Lucas representation, the 3-adic limit, and the product formula are not claimed. The sequence is defined by the NAME recurrence.

**Definition 1.1 (The integer cubic recurrence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 7\\\forall n \in \mathbb{N},\; \operatorname{a}\left(n + 1\right) = \operatorname{a}\left(n\right) \cdot (\operatorname{a}\left(n\right)^{2} - 3)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/BalaCubicThreeAdicCongruence.a` (`✓ std3`).

*Citation.* N. J. A. Sloane; Peter Bala (2022). *OEIS A002000, the cubic recurrence a(n+1) = a(n)(a(n)^2 - 3) from 7, with Bala's 3-adic congruence conjecture*. URL: <https://oeis.org/A002000>.

*Commentary.*

The initial value is 7. Each next term is the current term multiplied by its square minus 3. Both subtraction and multiplication take place in the integers.

**Theorem 1.2 (The growing-modulus congruence).**

$$\forall n \in \mathbb{N}, r \in \mathbb{N},\; (r \le n) \Rightarrow ((3: \mathbb{Z})^{n + r + 2} \mid \operatorname{a}\left(n + 1\right) - \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BalaCubicThreeAdicCongruence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a002000-bala-cubic-three-adic-congruence` (proved) by `D5/S1/Recurrence/BalaCubicThreeAdicCongruence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a002000-bala-cubic-three-adic-congruence","declaration_gid":"D5/S1/Recurrence/BalaCubicThreeAdicCongruence.result","resolution_kind":"proved"} -->

*Citation.* N. J. A. Sloane; Peter Bala (2022). *OEIS A002000, the cubic recurrence a(n+1) = a(n)(a(n)^2 - 3) from 7, with Bala's 3-adic congruence conjecture*. URL: <https://oeis.org/A002000>.

*Commentary.*

Induction gives 3^(2n+2) ∣ a(n)+2. The initial value plus 2 is 9, and a(n+1)+2=(a(n)-1)^2(a(n)+2). Since 3 divides a(n)+2, it also divides a(n)-1, supplying two further powers of 3 at each step. The difference factors as a(n+1)-a(n)=a(n)(a(n)-2)(a(n)+2). Finally, r<=n gives n+r+2<=2n+2, so the desired power divides the difference.

## References

- Truth anchor: `D5/S1/Recurrence/BalaCubicThreeAdicCongruence.a`
- Truth anchor: `D5/S1/Recurrence/BalaCubicThreeAdicCongruence.result`
