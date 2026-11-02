# A failure of the even Kimoto–Wakayama congruence

## Abstract

The normalized even Apéry-like ratio at (p,m,n,s) = (3,5,2,7) fails modulo nine.

**Definition 1.1 (The normalized numbers of even weight).**

$$\forall (s: \mathbb{N}), (((\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, 0\right): \mathbb{Q}) = \operatorname{ite}\left(s = 0, (1: \mathbb{Q}), (0: \mathbb{Q})\right)) \land (((\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, 1\right): \mathbb{Q}) = \operatorname{ite}\left(s = 0, \frac{(3: \mathbb{Q})}{(4: \mathbb{Q})}, \operatorname{ite}\left(s = 1, (1: \mathbb{Q}), (0: \mathbb{Q})\right)\right)) \land (\forall (j: \mathbb{N}), ((2 \le j) \to ((\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, j\right): \mathbb{Q}) = \frac{(8 \cdot ((\operatorname{Nat.cast}\left(j\right): \mathbb{Q}))^{2} - 8 \cdot (\operatorname{Nat.cast}\left(j\right): \mathbb{Q}) + 3) \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, j - 1\right) - 4 \cdot ((\operatorname{Nat.cast}\left(j - 1\right): \mathbb{Q}))^{2} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, j - 2\right) + 4 \cdot \operatorname{ite}\left(s = 0, (0: \mathbb{Q}), \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s - 1, j - 1\right)\right)}{4 \cdot ((\operatorname{Nat.cast}\left(j\right): \mathbb{Q}))^{2}})))))$$

*Formalization.* `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.normalizedEven` (`✓ std3`).

*Citation.* Kimoto, Kazufumi; Wakayama, Masato (2022). *Apéry-like numbers for non-commutative harmonic oscillators and automorphic integrals*. DOI: [10.4171/aihpd/129](https://doi.org/10.4171/aihpd/129). URL: <https://arxiv.org/abs/1905.01775v2>.

*Commentary.*

The rational number normalizedEven(s,j) is the normalized Apéry-like number of weight 2s+2 at j. The initial values and recurrence specify it for every natural s and j. The lower-weight term is zero when s=0, so the weight-zero row is identically zero. Subtraction in the indices is natural subtraction; the recurrence is used only for j at least two. Section 3.4 of Kimoto and Wakayama gives the recurrence and initial values (arXiv v2 TeX, lines 1431–1470, especially 1446–1448 and 1450–1466).

**Definition 1.2 (Congruence of rational numbers).**

$$\forall (p: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (x: \mathbb{Q}), (\forall (y: \mathbb{Q}), ((\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.RatCongr}\left(p, n, x, y\right)) \Leftrightarrow (\exists (a: \mathbb{Z}), (\exists (b: \mathbb{Z}), ((\neg ((\operatorname{Nat.cast}\left(p\right): \mathbb{Z}) \mid b)) \land ((x - y) \cdot (\operatorname{Int.cast}\left(b\right): \mathbb{Q}) = ((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{n} \cdot (\operatorname{Int.cast}\left(a\right): \mathbb{Q})))))))))$$

*Formalization.* `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.RatCongr` (`✓ std3`).

*Citation.* Kimoto, Kazufumi; Wakayama, Masato (2022). *Apéry-like numbers for non-commutative harmonic oscillators and automorphic integrals*. DOI: [10.4171/aihpd/129](https://doi.org/10.4171/aihpd/129). URL: <https://arxiv.org/abs/1905.01775v2>.

*Commentary.*

RatCongr(p,n,x,y) means that x−y is p to the power n times a rational number admitting an integer denominator indivisible by p. Its definition uses integer a and b, with no primality assumption on p. For prime p the condition on b also makes b nonzero, so multiplying by b gives precisely congruence in the localization of the integers away from p. This is the meaning of rational congruence in the even assertion of Conjecture 3.6 (arXiv v2 TeX, lines 1608–1617). The casts of p to an integer and of p, a and b to rational numbers are shown explicitly.

**Definition 1.3 (The even assertion restricted to odd primes).**

$$(\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.claim}) \Leftrightarrow (\forall (p: \mathbb{N}), ((\operatorname{Nat.Prime}\left(p\right)) \to ((p \ne 2) \to (\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (s: \mathbb{N}), ((0 < m) \to ((0 < n) \to ((0 < s) \to ((s \le m \cdot p) \to ((s \le m \cdot (p)^{n - 1}) \to ((\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.RatCongr}\left(p, n, \frac{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s \cdot n} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot (p)^{n}\right)}{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot p\right)}, \frac{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s \cdot \left(n - 1\right)} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot (p)^{n - 1}\right)}{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot p\right)}\right)) \land (\neg (\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.RatCongr}\left(p, n, \frac{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s \cdot \left(n - 1\right)} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot (p)^{n - 1}\right)}{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot p\right)}, (0: \mathbb{Q})\right)))))))))))))))$$

*Formalization.* `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kimoto, Kazufumi; Wakayama, Masato (2022). *Apéry-like numbers for non-commutative harmonic oscillators and automorphic integrals*. DOI: [10.4171/aihpd/129](https://doi.org/10.4171/aihpd/129). URL: <https://arxiv.org/abs/1905.01775v2>.

*Commentary.*

Conjecture 3.6 gives the following even assertion (arXiv v2 TeX, lines 1608–1617): “For positive integers $m,n,s$ such that $m \cdot p \ge s$ and $m \cdot (p)^{n - 1} \ge s$, we have

$$
\frac{(p)^{2 \cdot s \cdot n} \cdot \left(\widetilde{J}_{2 \cdot s + 2}\right)\left(m \cdot (p)^{n}\right)}{(p)^{2 \cdot s} \cdot \left(\widetilde{J}_{2 \cdot s + 2}\right)\left(m \cdot p\right)} \equiv \frac{(p)^{2 \cdot s \cdot \left(n - 1\right)} \cdot \left(\widetilde{J}_{2 \cdot s + 2}\right)\left(m \cdot (p)^{n - 1}\right)}{(p)^{2 \cdot s} \cdot \left(\widetilde{J}_{2 \cdot s + 2}\right)\left(m \cdot p\right)} (\neg\equiv0) \pmod{(p)^{n}}
$$

” Here claim quantifies only over odd primes p, expressed by Nat.Prime p and p≠2. It is therefore a weaker assertion than the source assertion allowing all primes, and its failure also refutes that assertion. The source subsequently assumes odd primes in the subsection (TeX line 1635). The two conclusions are congruence of the displayed ratios and noncongruence of the right ratio to zero. All divisions are rational divisions, including the total value zero for division by zero; no additional nonzero-denominator hypothesis is imposed.

**Theorem 1.4 (The assertion fails at p=3, m=5, n=2, s=7).**

$$\neg (\forall (p: \mathbb{N}), ((\operatorname{Nat.Prime}\left(p\right)) \to ((p \ne 2) \to (\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (s: \mathbb{N}), ((0 < m) \to ((0 < n) \to ((0 < s) \to ((s \le m \cdot p) \to ((s \le m \cdot (p)^{n - 1}) \to ((\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.RatCongr}\left(p, n, \frac{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s \cdot n} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot (p)^{n}\right)}{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot p\right)}, \frac{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s \cdot \left(n - 1\right)} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot (p)^{n - 1}\right)}{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot p\right)}\right)) \land (\neg (\operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.RatCongr}\left(p, n, \frac{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s \cdot \left(n - 1\right)} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot (p)^{n - 1}\right)}{((\operatorname{Nat.cast}\left(p\right): \mathbb{Q}))^{2 \cdot s} \cdot \operatorname{D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation.normalizedEven}\left(s, m \cdot p\right)}, (0: \mathbb{Q})\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kimoto-wakayama-2019-even-normalized-apery-congruence` (refuted) by `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kimoto-wakayama-2019-even-normalized-apery-congruence","declaration_gid":"D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kimoto, Kazufumi; Wakayama, Masato (2022). *Apéry-like numbers for non-commutative harmonic oscillators and automorphic integrals*. DOI: [10.4171/aihpd/129](https://doi.org/10.4171/aihpd/129). URL: <https://arxiv.org/abs/1905.01775v2>.

*Commentary.*

Compute the eight entries with weight indices zero through seven by keeping two consecutive rows. Before the row at j=0, the previous row is zero; the row at zero is (1,0,0,0,0,0,0,0), and the row at one is (3/4,1,0,0,0,0,0,0). Each later row uses the recurrence, including the preceding row's entry of one lower weight. Continuing through j=45 gives the entries at j=15 and j=45 for weight sixteen. In particular, normalizedEven(7,15) = 7333120509469805428121 / 355769406331851217305600000.

These exact values give the left ratio L = 3²⁸ normalizedEven(7,45) / (3¹⁴ normalizedEven(7,15)) as P/Q, where P = 102790658465770739117540100122976721847176041588902154700374527298060572494857673559242663743632025784157718049052857 and Q = 248060981949704625896344570711464099546609864372154310051109270678757921001761367078238673489100800000000000. The right ratio is 3¹⁴ normalizedEven(7,15) divided by itself. Its denominator is nonzero by the value at fifteen, so it equals one.

If RatCongr(3,2,P/Q,1) held, there would be integers a and b with 3 not dividing b and (P/Q−1)b=9a. Subtracting one and clearing the nonzero integer Q gives (P−Q)b=9aQ as an integer equality. Taking remainders modulo nine uses P−Q≡3 and forces 3b≡0 modulo nine. Thus 3 divides b, a contradiction.

Finally, three is an odd prime, m=5, n=2 and s=7 are positive, and both required bounds reduce to 7≤15. If claim held, its congruence conclusion at these parameters would be RatCongr(3,2,L,1), contrary to the preceding calculation. The congruence conclusion alone already fails; the assertion about odd weights and any corrected even congruence are not conclusions of this argument.

## References

- Truth anchor: `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.RatCongr`
- Truth anchor: `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.normalizedEven`
- Truth anchor: `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.result`
