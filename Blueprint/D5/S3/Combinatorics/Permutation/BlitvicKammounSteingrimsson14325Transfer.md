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

**Theorem 1.3 (Positive transfer rows are shifted Catalan numbers modulo four).**

$$\forall n: \mathbb{N}, \left(b_{n + 2}\right)\left(3\right) = 3 \cdot C_{n + 2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_catalan_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Cₙ is the ordinary nth Catalan number. For every n≥0 the formula is (row ℕ (n+1) 3 : ZMod 4)=3Cₙ₊₂; the omitted initial row is row (ZMod 4) 0 3=1. Let C be the Catalan generating series over ZMod 4, V=3C²−2 and U=1+XV. The imported Catalan equation gives V+2XV+X²V²=1, hence U=(1+2X)V+XUV and V=UV−XV². The series attached to odd argument 4m+1 is UVᵐ, and that attached to 4m+3 is Vᵐ⁺¹. Their adjacent identities imply the full sum recurrence; all constant coefficients are one. Induction on row degree using odd_row_recurrence identifies every coefficient. At argument three the series is V, whose positive coefficients are three times the next Catalan numbers. This is a universal formal-series argument, with no finite-range inference and no division by a nonunit in ZMod 4.

**Theorem 1.4 (The exact dyadic modulo-ten rule for all transfer rows).**

$$\forall n: \mathbb{N}, mod\left(rowNat\left(n, 3\right), 10\right) = dyadicResidue{n + 2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The notation dyadicResidue(m) means one if m=2ᵏ for some k≥1, and six otherwise. The source row index is j=n+1, so the exception is precisely j+1=2ᵏ with k≥1. For a positive row index, reduce the Catalan formula from ZMod 4 to ZMod 2 through the canonical ring homomorphism. The existing binary_catalan theorem then gives oddness exactly at dyadic indices. The constant initial row supplies the n=0 boundary. Reduction of natural rows to ZMod 5 and row_mod_five give residue one modulo five. Elementary arithmetic combines the two residues to obtain one or six modulo ten. This theorem concerns natural transfer rows only; it assumes no recurrence for the actual packing count.

**Theorem 1.5 (The exact two-power exception set for transfer rows).**

$$\forall n: \mathbb{N}, fourNondivides{rowNat\left(n, 3\right)} \iff \exists i,p: \mathbb{N}, p \leq i and n + 2 = 2^{i} + 2^{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_four_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n≥0, four fails to divide row ℕ n 3 exactly when n+2 is a sum of two powers of two with p≤i. The same-exponent case represents a single power of two; the p=0<i case represents odd integers with two occupied bits. Let s(m) be the sum of the base-two digits of m. The proof establishes s(m+1)+v₂(m+1)=s(m)+1 by binary induction. Kummer's imported digit-sum formula gives v₂(binomial(2m,m))=s(m); the imported identity (m+1)Cₘ=binomial(2m,m) then yields v₂(Cₘ)+1=s(m+1). A separate binary induction and a direct shift calculation characterize s(m)≤2, for m≥2, as the exact two-power set. The Catalan row formula and the unit three transfer this characterization to every positive row; the initial row supplies the equal-exponent pair i=p=0. Both implications hold universally. The Core module proves the actual grid-to-row bijection and applies this law to actual permutations.

The source target counts actual permutations of [3j+2], j≥1, whose prescribed length-five windows at starts 1+3t, 0≤t<j, have pattern 14325. Extra occurrences are allowed. The Core module proves an insertion/deletion bijection identifying this count with row ℕ (j−1) 3. Natural-to-residue reduction is proved inside the Catalan formula, and the Core module applies both row laws to the actual count.

The full target also requires residue one modulo ten when j+1=2ᵏ with k≥1, residue six otherwise, and nondivisibility by four if and only if j+1=2ⁱ+2ᵖ with 0≤p≤i. The equal-exponent and p=0 boundaries are included. The printed continuation says four divides all but these indices; the exact-exception converse is the stronger registered interpretation. The Core module proves both exact actual-count conclusions using these transfer results.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.odd_row_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_catalan_mod_four`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_five`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_four_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.row_mod_ten`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../../../S1/Recurrence/Invariants/CatalanCompositionSquareParity.md)
