# Signed transpositions of Borcherds coefficients

## Abstract

Signed transpositions of Borcherds coefficients

Let a_n b denote a family of bilinear integer modes on a complex module. Lower truncation means that a_n b vanishes for all sufficiently large n for each pair of states. Write D(a,b,c;p,q,r) for the forward product minus (-1)^r times the reverse product minus the iterate, with p, q and r arbitrary integers. The binomial coefficients have integer upper indices. Write T^[j] for T^j/j! for a linear endomorphism T.

**Theorem 1.1 (The coefficient identity as vanishing of the defect).**

Lean statement: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_eq_zero_iff_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_eq_zero_iff_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under lower truncation, D(a,b,c;p,q,r) vanishes exactly when the Borcherds coefficient identity holds with all three summands finitely supported. The inner modes b_(q+i) c, a_(p+i) c and a_(r+i) b vanish for sufficiently large i, respectively. Bilinearity then kills the summands.

**Theorem 1.2 (Exchange of the first two states).**

Lean statement: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_first`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under lower truncation, coefficient skew for (a,b) and the divided state translation law, D(a,b,c;p,q,r) equals (-1)^(r+1) times D(b,a,c;q,p,r). The skew expansion of the iterate is supported on i+j<N by truncation of b_(r+i+j) a. Summing along i+j fixed uses binomial reflection and Vandermonde convolution, via Mathlib's Ring.choose_neg and Ring.add_choose_eq.

**Theorem 1.3 (Exchange of the last two states).**

Lean statement: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_last`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under lower truncation and the divided mode translation law for a, assume coefficient skew for (b,c), for (a_(r+i) b,c), and for (b,a_(p+i) c) at every natural i in the two composite families. Then D(a,b,c;p,q,r) is the sum over j at least zero of (-1)^(q+j+1) times T^[j] applied to D(a,c,b;r,q+j,p). The shifted defects themselves have finite support in j. The forward branch has a cutoff from truncation of c_(q+j+i) b. Each composite branch has only finitely many nonzero inner states, and the maximum of their truncation cutoffs bounds j.

## References

- Truth anchor: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_eq_zero_iff_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_first`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_last`
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](../StateFieldResidueReconstruction.md)
