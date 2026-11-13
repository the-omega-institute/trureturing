# A conditional progression interpretation of Wu's third conjecture for A227244

## Abstract

Under two independent progression noncoverage hypotheses, 149 is the least prime divisor for every natural index.

All indices and exponents are natural numbers. The outer arithmetic, including the final subtraction, is in the integers. The symbol G denotes the signed integer itself, without a natural subtraction or absolute value.

The symbol G is the public original-owner definition D5.S3.Arith.Primes.WuA227244ConjectureFour.G, used directly throughout the Lean proof. OEIS A227244, NAME: Smallest prime factor of (2^(2^n) + 1)*2^(2^(2^n)) - 1. The exponent of the second outer power is two raised to two raised to m.

$\forall m \in \mathbb{N},\; \operatorname{G}\left(m\right) = ((2: \mathbb{Z})^{2^{m}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{m}}} - 1$

Write a(m) for the least prime divisor of G(m). For all natural m, 2^m is at least 1, so the first factor of G(m)+1 is at least 3 and the second at least 4; hence G(m) is at least 11. The assertion a(m)=P means that P is prime, the integer P divides this same signed G(m), and P is no larger than every natural prime divisor of G(m).

The exact natural-index intersections are (there exists k1 in N with 72*n+32=20*k1+16) if and only if n mod 5=2, and (there exists k2 in N with 72*n+32=220*k2+8) if and only if n mod 55=18. The k1 and k2 witnesses are independent; neither is required to equal n or the other witness. In the forward directions the equations give 12*n congruent to 4 modulo 20 and 72*n congruent to 196 modulo 220, respectively. Dividing out the common factor 4 gives 3*n congruent to 1 modulo 5 and 18*n congruent to 49 modulo 55. The respective inverses are 2 modulo 5 and 52 modulo 55, so n is congruent to 2 modulo 5 and to 18 modulo 55, respectively. Conversely, writing n=5*h+2 gives k1=18*h+8, and writing n=55*h+18 gives k2=18*h+6. All these witnesses are natural, including h=0. The two exceptional sets are disjoint: n mod 55=18 entails n mod 5=3, which excludes n mod 5=2.

Consequently, for every natural n including zero, a(72*n+32)=101 when n mod 5=2, a(72*n+32)=47 when n mod 55=18, and a(72*n+32)=149 when both residue conditions fail. For the first exceptional set substitute k1 into D5.S3.Arith.Congruence.WuA227244C1Equality.result: it supplies primality of 101, divisibility of G(20*k1+16), and the lower bound against every prime divisor. The index equality transports all three clauses to G(72*n+32). The second exceptional set uses k2 and D5.S3.Arith.Congruence.WuA227244C2Equality.result in exactly the same way, with prime 47. On the complement the two equivalences give the two separate noncoverage hypotheses of result below, which supplies the complete least-prime triple for 149. In particular a(176)=101 and a(1328)=47; these values show why the unconditional equality to 149 would fail, while preserving the conditional assertion below.

The parameter correspondence for the modular reduction is s=72 and t=32, with d=q-1. For the exceptional primes the rows are (q,d,p,L)=(47,46,11,55) and (101,100,20,5), with zero residues 18 and 2. The target row is (149,148,36,1), with zero residue 0. Every other odd prime below 149 has an empty zero set, and parity excludes 2. The q=107 row uses (d,p,L)=(106,52,13): its tail bound is 52<=2^32, so a replacement bound p<=t would discard a required case. The general reduction and its five hypotheses are explained at the original progression_reduce and tail_reduce owner, WuA227244ConjectureFour.

**Definition 1.1 (Finite residues of the nested powers).**

$$\forall q \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{reduced}\left(q, d, p, L, r\right) = ((2: \operatorname{ZMod}\left(q\right))^{\operatorname{mod}\left(2^{72 \cdot r + 32}, d\right)} + 1) \cdot (2: \operatorname{ZMod}\left(q\right))^{\operatorname{mod}\left(2^{p + \operatorname{mod}\left(2^{72 \cdot r + 32}, p\right)}, d\right)} - 1$$

*Formalization.* `D5/S3/Arith/Primes/WuA227244ConjectureThree.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 3 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

This residue expression is in ZMod q. Its five natural parameters are q, d, p, L and r; L records the period used to choose r. The first exponent is reduced modulo d. For the second exponent, a tail of length p precedes reduction modulo p, and the resulting outer exponent is reduced modulo d. Periodicity of powers along 72*n+32 transfers this expression to every natural n.

**Theorem 1.2 (The exact conditional least-prime assertion).**

$$\forall n \in \mathbb{N},\; (\neg (\exists k \in \mathbb{N},\; 72 \cdot n + 32 = 20 \cdot k + 16)) \Rightarrow ((\neg (\exists k \in \mathbb{N},\; 72 \cdot n + 32 = 220 \cdot k + 8)) \Rightarrow ((\operatorname{Prime}\left(149\right)) \land (((149: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{72 \cdot n + 32}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{72 \cdot n + 32}}} - 1) \land (\forall q \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \Rightarrow (((q: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{72 \cdot n + 32}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{72 \cdot n + 32}}} - 1) \Rightarrow (149 \le q))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-a227244-conjecture-three` (proved) by `D5/S3/Arith/Primes/WuA227244ConjectureThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-a227244-conjecture-three","declaration_gid":"D5/S3/Arith/Primes/WuA227244ConjectureThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 3 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

The source says: Conjecture 3: a(72*n+32) = 149 for n >= 0 and a(72*n+32) is not covered by Conjectures 1 and 2. We use the disclosed progression-index CONDITIONAL interpretation: for each natural n, absence of a natural k with 72*n+32=20*k+16 and, independently, absence of a natural k with 72*n+32=220*k+8 imply the least-prime conclusion. This quantified formula is our interpretation, not an author-written formula or established author intent. Both k binders range independently over all natural numbers, including zero; n also includes zero and is unbounded. The first hypothesis gives n mod 5 different from 2 and excludes the prime 101; the second gives n mod 55 different from 18 and excludes 47. Periodic modular transfer proves divisibility by 149 and excludes all 34 smaller primes. No extra exclusion, finite prefix or eventual onset is assumed. The proof composes existing periodicity, casts and finite calculations; it claims no new general method

## References

- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureThree.reduced`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureThree.result`
- Dependency: [D5/S3/Arith/Primes/WuA227244ConjectureFour](WuA227244ConjectureFour.md)
