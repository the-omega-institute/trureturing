# Wu's fourth conjecture for A227244

## Abstract

Fifty-nine is the least prime divisor throughout the specified progression outside one residue class.

All indices and exponents are natural numbers. The outer arithmetic, including the final subtraction, is in the integers. The symbol G denotes the signed integer itself, without a natural subtraction or absolute value.

**Definition 1.1 (The nested exponential integer).**

$$\forall m \in \mathbb{N},\; \operatorname{G}\left(m\right) = ((2: \mathbb{Z})^{2^{m}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{m}}} - 1$$

*Formalization.* `D5/S3/Arith/Primes/WuA227244ConjectureFour.G` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

OEIS A227244, NAME: Smallest prime factor of (2^(2^n) + 1)*2^(2^(2^n)) - 1. The exponent of the second outer power is two raised to two raised to m.

**Definition 1.2 (The least-prime assertion).**

$$claim = (\forall n \in \mathbb{N},\; (\operatorname{mod}\left(n, 55\right) \neq 26) \Rightarrow ((\operatorname{Prime}\left(59\right)) \land (((59: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{168 \cdot n + 43}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{168 \cdot n + 43}}} - 1) \land (\forall q \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \Rightarrow (((q: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{168 \cdot n + 43}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{168 \cdot n + 43}}} - 1) \Rightarrow (59 \le q))))))$$

*Formalization.* `D5/S3/Arith/Primes/WuA227244ConjectureFour.claim` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

OEIS A227244, FORMULA, Chai Wah Wu: Conjecture 4: a(168*n+43) = 59 if n>=0 and n mod 55 <> 26. Least prime divisor means primality of 59, divisibility by 59, and a lower bound on every natural prime divisor of that same signed integer. The assertion includes n=0 and has no upper bound. It makes no assertion at residue 26 and does not assert that the exclusion is necessary.

**Theorem 1.3 (Powers along an arithmetic progression).**

$$\forall M \in Type*,\; \forall inst \in \operatorname{CommMonoid}\left(M\right),\; \forall a \in M,\; \forall s \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; (a^{s \cdot L + t} = a^{t}) \Rightarrow (a^{s \cdot n + t} = a^{s \cdot \operatorname{mod}\left(n, L\right) + t})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureFour.progression_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

For every type M with a commutative monoid structure, a in M and natural s, t, L and n, the equation a^(s*L+t)=a^t implies a^(s*n+t)=a^(s*(n mod L)+t). There is no positivity hypothesis on L. This is the canonical reduction used by formula_reduce here and directly by the C1 and C2 formula_reduce proofs. It supplies no new mathematical content.

**Theorem 1.4 (Powers after an initial tail).**

$$\forall M \in Type*,\; \forall inst \in \operatorname{CommMonoid}\left(M\right),\; \forall a \in M,\; \forall p \in \mathbb{N},\; \forall e \in \mathbb{N},\; (a^{p + p} = a^{p}) \Rightarrow ((p \le e) \Rightarrow (a^{e} = a^{p + \operatorname{mod}\left(e, p\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureFour.tail_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

For every type M with a commutative monoid structure, a in M and natural p and e, the equation a^(p+p)=a^p together with p<=e implies a^e=a^(p+e mod p). There is no positivity hypothesis on p. This is the canonical tail reduction used by formula_reduce here and directly by the C1 and C2 formula_reduce proofs. It supplies no new mathematical content.

**Definition 1.5 (Finite residues of the nested powers).**

$$\forall q \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{reduced}\left(q, d, p, L, r\right) = ((2: \operatorname{ZMod}\left(q\right))^{\operatorname{mod}\left(2^{168 \cdot r + 43}, d\right)} + 1) \cdot (2: \operatorname{ZMod}\left(q\right))^{\operatorname{mod}\left(2^{p + \operatorname{mod}\left(2^{168 \cdot r + 43}, p\right)}, d\right)} - 1$$

*Formalization.* `D5/S3/Arith/Primes/WuA227244ConjectureFour.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

This residue expression is in ZMod q. Its five natural parameters are q, d, p, L and r; L records the period used to choose r. The first exponent is reduced modulo d. For the second exponent, a tail of length p precedes reduction modulo p, and the resulting outer exponent is reduced modulo d. Periodicity of powers along 168*n+43 transfers this expression to every natural n.

**Theorem 1.6 (The fourth conjecture holds).**

$$\forall n \in \mathbb{N},\; (\operatorname{mod}\left(n, 55\right) \neq 26) \Rightarrow ((\operatorname{Prime}\left(59\right)) \land (((59: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{168 \cdot n + 43}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{168 \cdot n + 43}}} - 1) \land (\forall q \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \Rightarrow (((q: \mathbb{Z}) \mid ((2: \mathbb{Z})^{2^{168 \cdot n + 43}} + 1) \cdot (2: \mathbb{Z})^{2^{2^{168 \cdot n + 43}}} - 1) \Rightarrow (59 \le q)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-a227244-conjecture-four` (proved) by `D5/S3/Arith/Primes/WuA227244ConjectureFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-a227244-conjecture-four","declaration_gid":"D5/S3/Arith/Primes/WuA227244ConjectureFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

Powers along an arithmetic progression repeat once a period equation holds. After the initial tail, the inner modular powers repeat as well. These two facts reduce divisibility by 59 and nondivisibility by each smaller prime to finite residue calculations. For the prime 47 the period in n is 55 and the calculation uses the stated exclusion of residue 26. Divisibility by 59 and exclusion of every smaller prime give the least-prime assertion for the entire unbounded family.

## References

- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureFour.G`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureFour.claim`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureFour.progression_reduce`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureFour.reduced`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureFour.result`
- Truth anchor: `D5/S3/Arith/Primes/WuA227244ConjectureFour.tail_reduce`
