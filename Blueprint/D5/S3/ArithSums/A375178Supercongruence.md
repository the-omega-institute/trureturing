# A375178: a fifth-power supercongruence

## Abstract

The A375178 binomial cube sum is one modulo the fifth power of every prime at least seven.

The sequence sums the cubes of choose(n+k-1,k) over natural k<n, including the empty sum at n=0. The theorem proves the p^5 conjecture in the OEIS comment for every prime p at least 7.

**Theorem 1.1 (Universal congruence).**

$$\forall p \in \mathbb{N},\; \left(Prime\left(p\right) \land 7 \le p\right) \Rightarrow a\left(p\right) \bmod p^{5} = 1 \bmod p^{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A375178Supercongruence.supercongruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2024). *A375178 — binomial cube sums and a fifth-power supercongruence*. URL: <https://oeis.org/A375178>.

*Commentary.*

Work in ZMod(p^5). For 0<k<p, expand the binomial coefficient as p/k times the product of 1+p/j for 1<=j<k. After cubing, only the constant and linear terms of that product remain.

Pairing k with p-k reduces the cubic harmonic sum modulo p^2 to the fourth-power sum modulo p. For the other term, reversal identifies the double harmonic sums H(1,3) and H(3,1). Their shuffle identity and the vanishing first and fourth power sums make both zero modulo p. The pinned finite-field power-sum theorem supplies these single sums.

The OEIS entry supplies the conjecture. Zhao's multiple harmonic sum results cover the harmonic prerequisites in the literature; the argument here proves them locally in Lean and connects them to the binomial sum. The conjectures for prime powers and the generalized family are separate questions.

## References

- Truth anchor: `D5/S3/ArithSums/A375178Supercongruence.supercongruence`
