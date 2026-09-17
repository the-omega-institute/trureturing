# Bala's Lucas Five-Adic Congruence

## Abstract

Bala's quintic recurrence satisfies the conjectured power-of-five congruence.

The symbol ℕ denotes the natural numbers including zero, and ℤ denotes the integers. The sequence a maps ℕ to ℤ; n and r are natural indices, and r≤n is their usual order relation. The symbol ∣ denotes integer divisibility; addition, subtraction, multiplication, and powers of sequence values are in ℤ, with natural exponents. Index arithmetic is in ℕ. Lucas denotes the Lucas sequence. The seed a(0)=1=Lucas(5^0) gives a(1)=11=A144837(1), agreeing with the OEIS offset 1. Only the Conjecture line in Peter Bala's Nov 14 2022 block is settled, for all n and r≤n, covering n≥1 and also n=0. The Lucas representation, the 5-adic limit (A269591), and A268922 are not claimed.

**Definition 1.1 (The integer quintic recurrence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 1\\\forall n \in \mathbb{N},\; \operatorname{a}\left(n + 1\right) = \operatorname{a}\left(n\right)^{5} + 5 \cdot \operatorname{a}\left(n\right)^{3} + 5 \cdot \operatorname{a}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/BalaLucasFiveAdicCongruence.a` (`✓ std3`).

*Citation.* Peter Bala (2022). *OEIS A144837, Lucas(5^n), with the 5-adic congruence conjecture a(n+1) ≡ a(n) (mod 5^(n+r+1))*. URL: <https://oeis.org/A144837>.

*Commentary.*

The initial value is 1. Each next term is the sum of the current term's fifth power, five times its cube, and five times the term. This is Bala's recurrence extended to index zero.

**Theorem 1.2 (The growing-modulus congruence).**

$$\forall n \in \mathbb{N}, r \in \mathbb{N},\; (r \le n) \Rightarrow ((5: \mathbb{Z})^{n + r + 1} \mid \operatorname{a}\left(n + 1\right) - \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BalaLucasFiveAdicCongruence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a144837-bala-lucas-five-adic-congruence` (proved) by `D5/S1/Recurrence/BalaLucasFiveAdicCongruence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a144837-bala-lucas-five-adic-congruence","declaration_gid":"D5/S1/Recurrence/BalaLucasFiveAdicCongruence.result","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A144837, Lucas(5^n), with the 5-adic congruence conjecture a(n+1) ≡ a(n) (mod 5^(n+r+1))*. URL: <https://oeis.org/A144837>.

*Commentary.*

Induction gives 5^(2n+1) ∣ a(n)^2+4. The initial square plus 4 is 5, and a(n+1)^2+4 equals (a(n)^4+3a(n)^2+1)^2(a(n)^2+4). The identity a(n)^4+3a(n)^2+1=(a(n)^2+4)(a(n)^2-1)+5 makes the squared factor divisible by 25. Thus each step gains two powers of 5. The difference factors as a(n+1)-a(n)=a(n)(a(n)^2+1)(a(n)^2+4). Finally, r≤n gives n+r+1≤2n+1 and the stated divisor.

## References

- Truth anchor: `D5/S1/Recurrence/BalaLucasFiveAdicCongruence.a`
- Truth anchor: `D5/S1/Recurrence/BalaLucasFiveAdicCongruence.result`
