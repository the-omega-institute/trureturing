# The 14325 grid transfer

## Abstract

Universal residue invariants of the grid transfer for the overlap-two 14325 problem.

For a semiring R define T(f)(k) as the sum of r f(r+2) over 1≤r≤k. The rows have b₁(k)=1 and bₙ₊₁=T(bₙ); Lean row R n is bₙ₊₁. All arguments k are natural, including the auxiliary values zero, one and two. This algebraic definition does not assert a packing-count recurrence as a hypothesis of the original problem.

**Theorem 1.1 (Every transfer row at argument three is one modulo five).**

$$\forall n: \mathbb{N}, row\left(ZMod\left(5\right), n, 3\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first nonconstant row has period-five profile (0,1,3,1,0). Its image has profile (0,1,1,1,0), which is fixed by T. The weighted increments of both profiles are (1,0,0,4,0). Induction on k proves these identities for every argument; induction on n proves stabilization. The initial row and first nonconstant row both take value one at three.

**Theorem 1.2 (Odd arguments over the ring of residues modulo four).**

$$\forall n, k: \mathbb{N}, \left(b_{n + 2}\right)\left(2 \cdot k + 1\right) = -\sum_{1 \leq r \leq k} \left(b_{n + 1}\right)\left(2 \cdot r + 1\right) + \left(2 \cdot k + 1\right) \cdot \left(b_{n + 1}\right)\left(2 \cdot k + 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.odd_row_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In ZMod 4 the exact formula is bₙ₊₂(2k+1)=−∑₁≤r≤k bₙ₊₁(2r+1)+(2k+1)bₙ₊₁(2k+3). For every row the values at 2h+2 and 2h+1 become equal after multiplication by two. In the constant row this is immediate; in a later row their difference is the even new summand. Pairing successive terms and using 2=−2 proves the reduced recurrence by induction on k. No division in ZMod 4 is used, and k=0 is retained.

The source target counts actual permutations of [3j+2], j≥1, whose prescribed length-five windows at starts 1+3t, 0≤t<j, have pattern 14325. Extra occurrences are allowed. Applying this invariant requires a proved insertion/deletion bijection identifying this count with row ℕ (j−1) 3 and a coefficient-reduction bridge. Those are separate obligations; no equality to the actual count is claimed here.

The full target also requires residue one modulo ten when j+1=2ᵏ with k≥1, residue six otherwise, and nondivisibility by four if and only if j+1=2ⁱ+2ᵖ with 0≤p≤i. The equal-exponent and p=0 boundaries are included. The printed continuation says four divides all but these indices; the exact-exception converse is the stronger registered interpretation. This contribution does not settle it or the full target. The narrower issue 21304 remains unchanged.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.odd_row_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_five`
