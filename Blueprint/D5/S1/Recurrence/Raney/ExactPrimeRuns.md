# Exact R31 Runs at Every Prime at Least Five

## Abstract

For every prime p at least five, the exact maximal zero-run lengths of the literal R31 sequence are its distinct positive record lengths.

This is the p≥5 branch of Theorem 2.1 of the repository theory input RANEY_R31_EXACT_ZERO_RUN_RECORD_SPECTRA, attributed there to Haobo Ma and Wenlin Zhang. The sequence is the existing raneyNumber(3,1,n), reduced in ZMod(p) after exact natural division. A maximal run uses IsMaximalDeltaInterval with Delta={0}, including both nonzero neighbors. The binary and ternary branches are separate mathematical obligations.

Write A(q,j)=ceil(jq/3)=(jq+2) div 3, B(q,1)=(q−3) div 2, B(q,2)=q−1, and ell(q,j)=B(q,j)+1−A(q,j), with natural subtraction and division. All q in the result are p^m with m≥1; they are odd and congruent to one or five modulo six.

**Theorem 1.1 (Complete maximal-run spectrum and first records).**

$$\forall p \in \mathbb{N},\; ((\operatorname{Prime}\left(p\right)) \land (5 \leq p)) \Rightarrow ((\forall m \in \mathbb{N},\; (1 \leq m) \Rightarrow (\forall j \in \mathbb{N},\; ((j = 1) \lor (j = 2)) \Rightarrow (((\operatorname{A}\left(p^{m}, j\right) \leq \operatorname{B}\left(p^{m}, j\right)) \Leftrightarrow ((j = 2) \lor ((p^{m} \neq 5) \land (p^{m} \neq 7)))) \land (\operatorname{ell}\left(p^{m}, j\right) = \operatorname{ite}\left(j = 1, \operatorname{ite}\left(\operatorname{mod}\left(p^{m}, 6\right) = 1, \operatorname{NatDiv}\left(p^{m} - 7, 6\right), \operatorname{NatDiv}\left(p^{m} - 5, 6\right)\right), \operatorname{NatDiv}\left(p^{m}, 3\right)\right)) \land ((\operatorname{A}\left(p^{m}, j\right) \leq \operatorname{B}\left(p^{m}, j\right)) \Rightarrow ((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), \operatorname{raneyResidue}\left(3, 1, p\right), \operatorname{A}\left(p^{m}, j\right), \operatorname{B}\left(p^{m}, j\right)\right)) \land (\forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; ((\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), \operatorname{raneyResidue}\left(3, 1, p\right), c, d\right)) \land (c < \operatorname{A}\left(p^{m}, j\right))) \Rightarrow (d + 1 - c < \operatorname{ell}\left(p^{m}, j\right)))))))) \land (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), \operatorname{raneyResidue}\left(3, 1, p\right), a, b\right)) \Rightarrow (\exists m \in \mathbb{N},\; \exists j \in \mathbb{N},\; (1 \leq m) \land ((j = 1) \lor (j = 2)) \land (\operatorname{A}\left(p^{m}, j\right) \leq \operatorname{B}\left(p^{m}, j\right)) \land (b + 1 - a = \operatorname{ell}\left(p^{m}, j\right)))) \land (\forall m \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; ((1 \leq m) \land (1 \leq h) \land ((j = 1) \lor (j = 2)) \land ((k = 1) \lor (k = 2)) \land ((m < h) \lor ((m = h) \land (j < k)))) \Rightarrow (\operatorname{ell}\left(p^{m}, j\right) < \operatorname{ell}\left(p^{h}, k\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/ExactPrimeRuns.raney_prime_ge_five_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

For every prime p≥5 and every m≥1, put q=p^m. The interval with j=1 is [ceil(q/3),(q−3)/2], and that with j=2 is [ceil(2q/3),q−1]. The first interval is empty precisely at q=5 and q=7; the second is always nonempty. Every retained interval is an actual maximal run. Every earlier maximal run has strictly smaller length, so this interval is both the earliest occurrence of its length and a record, also under the source convention allowing tied records.

Their lengths are ell(q,1)=(q−7)/6 for q congruent to one modulo six and (q−5)/6 for q congruent to five modulo six, and ell(q,2)=floor(q/3). Every actual maximal finite zero run has one of these retained lengths. The lengths strictly increase with m and, within each scale, from j=1 to j=2. Thus there are no duplicate retained values for a fixed prime, and the complete positive maximal-run and distinct positive record spectra coincide. All primes, exponents and interval endpoints are unbounded.

The proof derives raneyNumber(3,1,n)·n!·(2n+1)!=(3n)! from adjacent binomial identities and the literal quotient. Legendre's theorem then gives its p-adic valuation as the finite sum of f_(p^h)(n mod p^h), where f_q(x)=floor(3x/q)−floor((2x+1)/q). For x<q and q≥2 each summand is zero or one. The residue is zero exactly when some positive scale has summand one; scales beyond a sufficiently large power vanish. The proof does not assume a zero mask.

For q=p^m, solving f_q(x)=1 gives exactly the two displayed intervals. At each left neighbor, 3n+s=jq for s=1 or 2. At the first right neighbor, 2n+1=q; the second right neighbor is q. Reduction to every dividing lower scale makes its summand zero, and every higher summand vanishes by 3n+1<p^(m+1). These calculations prove both endpoint nonvanishing assertions.

Induct on the prime-power prefix. An actual run meeting a new scale interval equals it, since two maximal intervals sharing an index have equal endpoints. A disjoint run has no top-scale contribution. It cannot cross a multiple of the preceding power, where all lower contributions vanish. Taking its residues modulo that power produces an actual smaller-prefix run of equal length. The induction also proves that its start is no earlier than the unshifted witness for that length. This proves component completeness. Exact rounding and p≥5 give strict length growth, which excludes an equally long earlier run.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/ExactPrimeRuns.raney_prime_ge_five_spectrum`
- Dependency: [D5/S1/Recurrence/Raney/ZeroRunFamilies](ZeroRunFamilies.md)
