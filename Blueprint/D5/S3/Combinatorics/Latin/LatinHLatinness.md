# Latinness of the literal H family

## Abstract

The literal H square is Latin for every integer parameter at least nine.

**Theorem 1.1 (The literal H square is Latin).**

$$\forall K \in \mathrm{Int},\; 9 \le K \Rightarrow \operatorname{IsLatin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right), \operatorname{square}\left(\operatorname{toNat}\left(K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/LatinHLatinness.literal_h_latinness` (`✓ std3`). ∎

*Citation.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

For every integer K at least nine, put k equal to its natural representative and use the native order-four-k H square. Every fixed row and every fixed column is a bijection. The proof follows the priority delta table directly: residue equality is reduced to the zero, plus-one-modulus, or minus-one-modulus alternatives; the exceptional cap rows and columns, the parity-controlled bulk swaps, the K = 9 empty bulk, and the K = 10 first bulk block are all discharged in the same universal argument.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/LatinHLatinness.literal_h_latinness`
- Dependency: [D5/S3/Combinatorics/Latin/LatinHTransversals](LatinHTransversals.md)
