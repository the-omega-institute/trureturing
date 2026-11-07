# A missing square point forces a smaller Lee cover

## Abstract

Uniform upper bounds for arbitrary signed covering pairs in rank two.

**Theorem 1.1 (Odd coordinate divisibility fills the rotated square).**

Lean statement: `D5/S3/FiniteGroups/LeeSquareCompression.large_index_square_lift`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/LeeSquareCompression.large_index_square_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok and W. Kyle Beatty (2025). *On the diameter of undirected Cayley graphs of finite abelian groups*. DOI: [10.2140/cnt.2025.14.1](https://doi.org/10.2140/cnt.2025.14.1). URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let K be an integer relation lattice contained in cZ², with c odd and at least 3. Suppose the radius-s Lee ball covers Z²/K, where s is at least 3, and the actual quotient order exceeds 2s². Then the full square [−s,s]² covers Z²/TK for T(x,y)=(x+y,x−y). A missing point has opposite coordinate parities. Its two horizontal neighbors have square representatives whose first coordinates are forced to s and −s. Their relation difference gives c dividing 2(s+1), hence c dividing s+1.

Writing s+1=cq and restricting the original cover to cZ² gives a Lee cover of radius q−1 for the scaled relation lattice. Its quotient order is at most q²+(q−1)², the classical exact Lee-ball count. The actual index multiplies by c² under dilation. For s at least 3 this contradicts the assumed order. The excluded case c=3,s=2 is real: 3Z² has Lee radius 2, but (3,0) misses the lifted square. Determinant and quotient-index identities use Mathlib and the existing near-square lattice results.

**Theorem 1.2 (Every covering pair obeys the same order alternative).**

Lean statement: `D5/S3/FiniteGroups/LeeSquareCompression.arbitrary_pair_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/LeeSquareCompression.arbitrary_pair_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok and W. Kyle Beatty (2025). *On the diameter of undirected Cayley graphs of finite abelian groups*. DOI: [10.2140/cnt.2025.14.1](https://doi.org/10.2140/cnt.2025.14.1). URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

For c at least 2, k at least 1 and integer s at least 3, let arbitrary a,b in Z/c × Z/(ck) represent every group element by xa+yb with |x|+|y| at most s. Put N=c²k. Then N≤2s², or c is odd, c divides 2s+1, and 2N≤(2s+1)²−c². No regularity or chosen coordinate shape of a,b is required.

The coefficient map is surjective. Reduction modulo c induces a surjective endomorphism of (Z/c)², hence an injective one, so each kernel relation has both coordinates divisible by c. Its quotient index is exactly N. The sum-and-difference image has index 2N. Selecting a shortest residue progression in each square coordinate bounds this index by c² floor((2s+1)/c)². For even c the selected fiber already has equal parity; for odd c the square-lift result supplies it. Above 2s², the remainder must vanish. The odd square of the resulting quotient bounds the even integer 2k, producing the final subtraction of c².

This addresses the upper-bound mechanism toward Bajnok–Beatty Conjecture 1.6 in the stated invariant-factor targets. Matching constructions and the transfer from abstract finite groups are separate conclusions. The source comparison is arXiv:2406.04045v1; the revised body has not been read, and no current-publication novelty or priority claim is made.

**Theorem 1.3 (The common divisor controls the high-index branch).**

Lean statement: `D5/S3/FiniteGroups/LeeSquareCompression.lattice_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/LeeSquareCompression.lattice_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let K be any integer submodule of the integral plane, and let c,s be integers with c ≥ 2 and s ≥ 3. Suppose both coordinates of every vector in K are divisible by c, and every integral vector z has a representative r with |r₀|+|r₁| ≤ s and z−r in K. Then the actual additive-subgroup index I of K satisfies I ≤ 2s², or c is odd, c divides 2s+1, and 2I ≤ (2s+1)²−c². The statement assumes neither a product normal form nor a prescribed generating pair.

Above the baseline, square compression forces the remainder of 2s+1 modulo c to vanish. Thus the cofactor m=(2s+1)/c and c are odd. The scaled-index identity gives I=k c² for a natural k, and compression gives 2k ≤ m². Since m is odd, integrality sharpens this to 2k ≤ m²−1; multiplying by c² yields the square correction. BajnokBeattyFiniteUpper.finite_noncyclic_upper_dichotomy consumes this theorem for the actual coefficient kernel, using Smith normal form to obtain its common coordinate divisor and a quotient equivalence to identify I with the group cardinality. The source comparison is Bajnok–Beatty arXiv:2406.04045v1; no current literature novelty or priority is claimed.

## References

- Truth anchor: `D5/S3/FiniteGroups/LeeSquareCompression.arbitrary_pair_upper_bound`
- Truth anchor: `D5/S3/FiniteGroups/LeeSquareCompression.large_index_square_lift`
- Truth anchor: `D5/S3/FiniteGroups/LeeSquareCompression.lattice_upper_bound`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity](BajnokBeattyCayleyNecessity.md)
