# A conditional progression interpretation of Wu's third conjecture for A227244

## Abstract

Under two independent progression noncoverage hypotheses, 149 is the least prime divisor for every natural index.

All indices and exponents are natural numbers. The outer arithmetic, including the final subtraction, is in the integers. The symbol G denotes the signed integer itself, without a natural subtraction or absolute value.

**Definition 1.1 (The nested exponential integer).**

$$\forall m \in \mathbb{N},\; \operatorname{G}\left(m\right) = ((2: \mathbb{Z})^{2^{m}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{m}}} - 1$$

*Formalization.* `D5/S3/Arith/Primes/WuA227244ConjectureThree.G` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 3 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

OEIS A227244, NAME: Smallest prime factor of (2^(2^n) + 1)*2^(2^(2^n)) - 1. The exponent of the second outer power is two raised to two raised to m.

**Definition 1.2 (Finite residues of the nested powers).**

$$\forall q \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{reduced}\left(q, d, p, L, r\right) = ((2: \operatorname{ZMod}\left(q\right))^{\operatorname{mod}\left(2^{72 \cdot r + 32}, d\right)} + 1) \cdot (2: \operatorname{ZMod}\left(q\right))^{\operatorname{mod}\left(2^{p + \operatorname{mod}\left(2^{72 \cdot r + 32}, p\right)}, d\right)} - 1$$

*Formalization.* `D5/S3/Arith/Primes/WuA227244ConjectureThree.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 3 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

This residue expression is in ZMod q. Its five natural parameters are q, d, p, L and r; L records the period used to choose r. The first exponent is reduced modulo d. For the second exponent, a tail of length p precedes reduction modulo p, and the resulting outer exponent is reduced modulo d. Periodicity of powers along 72*n+32 transfers this expression to every natural n.

**Theorem 1.3 (The exact conditional least-prime assertion).**

$$\forall n \in \mathbb{N},\; (\neg (\exists k \in \mathbb{N},\; 72 \cdot n + 32 = 20 \cdot k + 16)) \Rightarrow ((\neg (\exists k \in \mathbb{N},\; 72 \cdot n + 32 = 220 \cdot k + 8)) \Rightarrow ((\operatorname{Prime}\left(149\right)) \land (((149: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{72 \cdot n + 32}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{72 \cdot n + 32}}} - 1) \land (\forall q \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \Rightarrow (((q: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{72 \cdot n + 32}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{72 \cdot n + 32}}} - 1) \Rightarrow (149 \le q))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-a227244-conjecture-three` (proved) by `D5/S3/Arith/Primes/WuA227244ConjectureThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-a227244-conjecture-three","declaration_gid":"D5/S3/Arith/Primes/WuA227244ConjectureThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 3 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

The source says: Conjecture 3: a(72*n+32) = 149 for n >= 0 and a(72*n+32) is not covered by Conjectures 1 and 2. We use the disclosed progression-index CONDITIONAL interpretation: for each natural n, absence of a natural k with 72*n+32=20*k+16 and, independently, absence of a natural k with 72*n+32=220*k+8 imply the least-prime conclusion. This quantified formula is our interpretation, not an author-written formula or established author intent. Both k binders range independently over all natural numbers, including zero; n also includes zero and is unbounded. The first hypothesis gives n mod 5 different from 2 and excludes the prime 101; the second gives n mod 55 different from 18 and excludes 47. Periodic modular transfer proves divisibility by 149 and excludes all 34 smaller primes. No extra exclusion, finite prefix or eventual onset is assumed. The proof composes existing periodicity, casts and finite calculations; it claims no new general method

## References

- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureThree.G`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureThree.reduced`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureThree.result`
