# Wu's fourth conjecture for A227244

## Abstract

The least prime divisor is 47 on residue 26 modulo 55 and 59 elsewhere in the fourth progression.

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

OEIS A227244, FORMULA, Chai Wah Wu: Conjecture 4: a(168*n+43) = 59 if n>=0 and n mod 55 <> 26. Least prime divisor means primality of 59, divisibility by 59, and a lower bound on every natural prime divisor of that same signed integer. The assertion includes n=0 and has no upper bound. This original assertion makes no assertion at residue 26. The complete classification derived below determines that residue as well.

**Theorem 1.3 (Powers along an arithmetic progression).**

$$\forall M \in Type*,\; \forall inst \in \operatorname{CommMonoid}\left(M\right),\; \forall a \in M,\; \forall s \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; (a^{s \cdot L + t} = a^{t}) \Rightarrow (a^{s \cdot n + t} = a^{s \cdot \operatorname{mod}\left(n, L\right) + t})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureFour.progression_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

For every type M with a commutative monoid structure, a in M and natural s, t, L and n, the equation a^(s*L+t)=a^t implies a^(s*n+t)=a^(s*(n mod L)+t). There is no positivity hypothesis on L. This is the canonical reduction used by formula_reduce here and directly by the C1, C2 and C3 formula_reduce proofs. It supplies no new mathematical content.

**Theorem 1.4 (Powers after an initial tail).**

$$\forall M \in Type*,\; \forall inst \in \operatorname{CommMonoid}\left(M\right),\; \forall a \in M,\; \forall p \in \mathbb{N},\; \forall e \in \mathbb{N},\; (a^{p + p} = a^{p}) \Rightarrow ((p \le e) \Rightarrow (a^{e} = a^{p + \operatorname{mod}\left(e, p\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA227244ConjectureFour.tail_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2026). *OEIS A227244, Conjecture 4 on the smallest prime factor*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

For every type M with a commutative monoid structure, a in M and natural p and e, the equation a^(p+p)=a^p together with p<=e implies a^e=a^(p+e mod p). There is no positivity hypothesis on p. This is the canonical tail reduction used by formula_reduce here and directly by the C1, C2 and C3 formula_reduce proofs. It supplies no new mathematical content.

For the general nested-power reduction, let q be an odd prime, set d=q-1, and let s,t,p,L be positive natural numbers. Assume all five conditions: (1) 2^d congruent to 1 modulo q; (2) 2^(2*p) congruent to 2^p modulo d; (3) 2^(s*L+t) congruent to 2^t modulo d; (4) 2^(s*L+t) congruent to 2^t modulo p; (5) p<=2^t. For 0<=r<L put E(r)=2^(s*r+t) and R(r)=((2^(E(r) mod d)+1)*2^((2^(p+(E(r) mod p))) mod d)-1) in ZMod q. Every exponent is a natural number; subtraction in G is integer subtraction and subtraction in R is in ZMod q. Then for every natural n, the image of G(s*n+t) in ZMod q equals R(n mod L). Since L>0, the chosen residue satisfies 0<=n mod L<L.

Here is the all-index derivation from progression_reduce and tail_reduce. Set m=s*n+t, r=n mod L, and mr=s*r+t. Apply progression_reduce with a=2 in ZMod d and then in ZMod p to obtain 2^m mod d=2^mr mod d and 2^m mod p=2^mr mod p. Since m>=t, monotonicity of natural powers gives p<=2^t<=2^m. Apply tail_reduce in ZMod d with e=2^m: 2^(2^m) mod d=2^(p+(2^m mod p)) mod d=2^(p+(2^mr mod p)) mod d. Finally 2^d=1 in ZMod q reduces both exponents in (2^(2^m)+1)*2^(2^(2^m))-1 modulo d. Substituting the two residue equalities gives R(r), including n=0. The progression and tail lemmas themselves have the stronger commutative-monoid domains stated above, without positive L or p. The odd-prime and positive-parameter assumptions specify the note's application; the five displayed conditions are retained explicitly.

The four progression substitutions are (s,t)=(20,16), (220,8), (72,32), and (168,43). Their formula_reduce proofs consume the same two monoid lemmas, the modular cast equalities and pow_eq_pow_mod. C1, C2 and C3 use the exponential tail bounds p<=2^16, p<=2^8 and p<=2^32. The local fourth-progression formula_reduce uses the sufficient stronger bound p<=43; it does not by itself supply the full positive-parameter statement. In particular the C3 row q=107 has p=52,t=32, which satisfies the required exponential bound. Finite residue tables establish the modular premises and the zero sets within one full period; the all-index transfer follows from the preceding argument.

Write a(m) for the least prime divisor of G(m), meaning the prime/divisibility/every-prime-divisor lower-bound triple. It is defined for every natural m since G(m)>=11: its two factors before subtracting 1 are at least 3 and 4. For every natural n, including zero, a(168*n+43)=47 if n mod 55=26, and a(168*n+43)=59 otherwise. The actual odd-index residue_47 identity uses (q,d,p,L)=(47,46,11,55); its value at residue 26 is zero. Thus 47 divides G(168*n+43) on that class. The existing unconditional nonzero_2 and nonzero_3 through nonzero_43 identities exclude each prime below 47 on every index. Together with primality of 47 these give the entire least-prime triple on the exceptional class. Off that class, nonzero_47 excludes 47, nonzero_53 excludes 53, and result below supplies the triple for 59. In particular a(168*n+43)=47 if and only if n mod 55=26: the other class has a prime divisor 59 and every prime divisor at least 59, contradicting divisibility by 47. The C2 result concerns even indices and is not used for this odd-index exception.

The fourth progression has zero set {26} for q=47,L=55 and zero set {0} for q=59,L=1, with (d,p)=(58,28) for the latter. All other odd primes below 59 have empty zero sets, and parity excludes 2. The corresponding C1 and C2 least-prime values are 101 on 20*n+16 and 47 on 220*n+8, supplied by their original equality results. The complete third progression, including its two disjoint intersections, is explained in WuA227244ConjectureThree. Bernard Schott's 2019 lower-bound work and Chai Wah Wu's 2026 identity a(4*n+5)=11 and C1 upper bound retain their original attribution. The four progression arguments do not settle individual-term primality assertions elsewhere in the OEIS comments or other Fermat-number questions.

The complete classification and the five-premise reduction are presented in Haobo Ma and Wenlin Zhang, Proof of Wu's four progression conjectures on least prime factors, outreach draft release outreach-task-shortnote-9a2584133276e304381aea9748610d7f in the-omega-institute/trureturing-outreach. Haobo Ma is affiliated with ChronoAI Pte Ltd, Singapore; Wenlin Zhang with the National University of Singapore and ChronoAI Pte Ltd, Singapore. The draft distinguishes the original four conditional or unconditional assertions from their exceptional-class consequences.

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
