# Connected nonnegative conductances on the original finite vertex set

## Abstract

Original harmonic-current resistance and mean-zero Rayleigh spectral interfaces.

All matrices use counting measure on Fin n. The weighted Laplacian, lambda2, Harmonic, effRes and totalRes are the original FiedlerResistanceInvariantWeightsRefutation objects. The sum is over all unordered distinct original vertex pairs, including nonedges. The matrix inverse supplies harmonic voltage and current; a spectral statistic is never used as a replacement definition of resistance. These are repository-derived interfaces consuming the original generic K2m supplier bodies and the pinned Hermitian spectral theorem, with no external novelty claim.

**Theorem 1.1 (Nonnegative conductances give the native positive semidefinite Laplacian).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.lap_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.lap_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, simple graph G on Fin n with decidable adjacency and total real Sym2 weight function w, coordinatewise nonnegativity on the actual edges implies that wLap G w is positive semidefinite. The proof derives the general double edge-energy identity; unused nonedge coordinates remain unrestricted.

**Theorem 1.2 (Harmonic resistance equals the full native reciprocal spectrum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.resistance_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.resistance_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive, every G and real w, if L=wLap G w is positive semidefinite and L+constProj n is positive definite, then the existing harmonic-current totalRes G w equals n times the sum of inverses of all native Hermitian eigenvalues of L. Zero eigenvalues have inverse zero. The proof constructs the unique harmonic extension at every distinct original pair from the inverse of L+constProj, identifies its positive current, sums all unordered original pairs including nonedges once, and directly applies the existing AlbrightKemenyEdgeDerivativeRefutation reciprocalRoots_eq_trace and reciprocalRoots_eq_sum suppliers.

**Theorem 1.3 (Positive connected conductances give the invertible shifted matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.positive_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.positive_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive, connected G and every w strictly positive on the original edges, L+constProj n is positive definite. A zero weighted edge energy forces equality of coordinates along every reachable path, hence a constant vector; the constant projection controls the remaining direction.

**Theorem 1.4 (Exactly one native zero eigenvalue).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.zero_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.zero_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive and every G,w with L+constProj n positive definite, exactly one index of the actual Hermitian eigenvalue enumeration has eigenvalue zero. The proof diagonalizes the original constant projector in the same eigenvector basis and uses its trace one.

**Theorem 1.5 (A centered matrix inequality bounds the actual Rayleigh quotient).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.psd_rayleigh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.psd_rayleigh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary n,G,w,t, positive semidefiniteness of L-t*(I-constProj n) implies t*dotProduct x x at most dotProduct x (L*x) for every x whose coordinate sum is zero.

**Theorem 1.6 (The actual mean-zero infimum is the positive spectral minimum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.lambda_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.lambda_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least two, every G,w with L positive semidefinite and L+constProj n positive definite, the actual lambda2 G w is positive; L-lambda2*(I-constProj n) is positive semidefinite; and every nonzero native eigenvalue is at least lambda2. The least nonzero indexed eigenvalue and its mean-zero eigenvector are certified with the original lambda2_eq_of_rayleigh.

**Theorem 1.7 (Actual normalization excludes a disconnected kernel).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.normalized_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.normalized_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive, L positive semidefinite and actual lambda2 G w equal to one imply L+constProj n positive definite. The infimum bounds every mean-zero vector, and centering an arbitrary vector gives the required matrix inequality.

**Definition 1.8 (The positive support keeps every original vertex).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.support`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary n,G,w, support G w has the same vertex set Fin n and adjacency G.Adj i j together with strict positivity of w on that original edge. There is no contraction or deletion of zero-degree vertices.

**Theorem 1.9 (Nonnegative normalized support is connected).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.connected_of_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.connected_of_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive, nonnegative weights on the original edges and positive definiteness of L+constProj n imply connectedness of support G w. The indicator of a hypothetical reachability component lies in the original Laplacian kernel; the shifted inverse forces it to be constant.

**Theorem 1.10 (A single excess eigenvalue forces a rank-one original matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.rankone_of_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.rankone_of_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive, arbitrary G,w with L+constProj n positive definite, t positive, and one native eigenvalue equal to 2*t while every other native eigenvalue is zero or t, there exists a real vector v on all original vertices with sum zero and squared counting norm one such that L-t*(I-constProj n)=t*vecMulVec v v, and this actual matrix has rank one. The proof conjugates the original matrix in its native unitary eigenbasis; it imposes no part-subspace invariance or rank premise.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.connected_of_shift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.lambda_spectral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.lap_psd`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.normalized_shift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.positive_shift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.psd_rayleigh`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.rankone_of_spectrum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.resistance_spectral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.support`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral.zero_count`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer](FiedlerResistanceK2mOptimizer.md)
