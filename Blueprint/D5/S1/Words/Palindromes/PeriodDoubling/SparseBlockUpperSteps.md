# Sparse Block Upper Constructions

## Abstract

Uniform four-cut and two-cut constructions for the sparse binary family.

**Theorem 1.1 (The two reductions and both endpoint bits).**

$$\forall p \in \mathbb{N},\; \forall z \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall eps \in \mathbb{N},\; \left(0 < p \land eps \le 1\right) \Rightarrow \left(\left(\left(\operatorname{mod}\left(z, 2\right) = 0 \land 3 \le c\right) \Rightarrow \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(p\right), \lambda s:\mathbb{N} \mapsto 2^{2 \cdot c + z + 2 + 3 \cdot s}\right) + \operatorname{sum}\left(\operatorname{range}\left(c\right), \lambda j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + eps\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) \le \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(\operatorname{NatSub}\left(p, 1\right)\right), \lambda s:\mathbb{N} \mapsto 2^{2 \cdot \operatorname{NatSub}\left(c, 3\right) + z + 9 + 2 + 3 \cdot s}\right) + \operatorname{sum}\left(\operatorname{range}\left(\operatorname{NatSub}\left(c, 3\right)\right), \lambda j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + eps\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) + 4\right) \land \left(\left(\operatorname{mod}\left(z, 2\right) = 1 \land 1 \le c\right) \Rightarrow \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(p\right), \lambda s:\mathbb{N} \mapsto 2^{2 \cdot c + z + 2 + 3 \cdot s}\right) + \operatorname{sum}\left(\operatorname{range}\left(c\right), \lambda j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + eps\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) \le \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(\operatorname{NatSub}\left(p, 1\right)\right), \lambda s:\mathbb{N} \mapsto 2^{2 \cdot \operatorname{NatSub}\left(c, 1\right) + z + 5 + 2 + 3 \cdot s}\right) + \operatorname{sum}\left(\operatorname{range}\left(\operatorname{NatSub}\left(c, 1\right)\right), \lambda j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + eps\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseBlockUpperSteps.sparse_block_upper_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed sums are the literal integers with binary blocks (100) repeated p times, a gap of z zeros and (10) repeated c times. For epsilon zero or one, an even gap and at least three tail blocks permit four cuts; an odd gap and at least one tail block permit two cuts. The construction uses the exact long and short odd-palindrome radii and preserves the higher prefix. NatSub is truncated natural subtraction; mod is natural remainder; val is the natural value of a finite index.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseBlockUpperSteps.sparse_block_upper_steps`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius](OddPalindromeRadius.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength](PalindromicLength.md)
