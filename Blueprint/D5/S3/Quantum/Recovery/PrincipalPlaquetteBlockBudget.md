# Coherent block budget for the one-party plaquette obstruction

## Abstract

Coherent rows strengthen the one-party plaquette obstruction for native paired channels.

**Theorem 1.1 (One squared diamond budget per coefficient row).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.matrixUnit_row_square_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.matrixUnit_row_square_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tagged rank-one test chooses the column amplitude vector proportional to all the errors in the row. It bounds their squared norm sum by the square of the native unhalved diamond distance.

**Theorem 1.2 (Improved one-party phase bound from coherent rows).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_improved_one_party_native_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_improved_one_party_native_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one selected pair of fibres the two row tests give a Frobenius budget. The opposite gauge converts entry errors into signed real budget deficits; a reciprocal variance identity then strengthens the cosine obstruction by a factor of the square root of two.

Only the first party's phase is used. The native paired-channel identity, labelled fibres and original target coefficients remain hypotheses. No assumption on leakage, common quotient or cross-entry dominance is added.

**Theorem 1.3 (Zero-phase obstruction from the coherent sum and both row budgets).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_sharp_zero_plaquette_native_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_sharp_zero_plaquette_native_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the first-party plaquette has zero phase, its gauged entries are nonnegative real. The flat rank-one test controls the signed sum of the four errors as well as the two row tests controlling their squared sum. A square-root inequality combines these budgets to give the square root of two minus one as a lower bound.

The formal theorem is a lower bound for a specified pair, not a guarantee that such a pair exists in the unrestricted problem. Attainment is not formalized here.

For comparison, a paper-level calibrated four-fibre example attains the bound. Set k to the square root of two minus one. Let u and v be unit vectors with real inner product minus k, and take fibre directions u, v, i u, i v. Each fibre has the orthonormal records formed by the sum and difference of its direction with a shared orthogonal unit vector, normalized by the square root of two. Use conjugate records on the other side. The selected first-side cross block has strictly positive entries.

In the per-fibre symmetric and antisymmetric bases, the Hermitian coefficient error is k times the direct sum of the four-cycle adjacency and a two-edge matching adjacency. Its absolute value has every original diagonal fibre block equal to k times the two-dimensional identity. The uniform input gives the normalized trace norm k, and the absolute-value dual majorant gives the matching upper bound in the calibrated trace-norm formula. The exact fixture and its semantics are not Lean claims here.

**Theorem 1.4 (A strict quarter obstruction on a first-party phase sector).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_quarter_plaquette_native_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_quarter_plaquette_native_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the first-party quarter-angle cosine is at least 0.899228, the unhalved native diamond error is strictly greater than a quarter. A pair of flat rank-one inputs with equal and alternating signs controls the real and imaginary parts of the gauge-projected error sum. The row-square budget and the two contraction sums then rule out the entire closed quarter sublevel.

The bound applies to the selected fibre pair, with the same paired dilation, labels and target as before. It neither establishes that one of the pairs must have this phase nor settles recovery for unrestricted channels.

The isolated two-fibre estimate cannot simply be continued to all phases. A calibrated example has cosine p = 2/sqrt(5) and diamond error exactly 1/4. In the following paper construction, J is the all-ones matrix, S is the alternating-sign matrix, and q is the square root of 1 minus p squared. The first cross block is (p J + i q S)/(2p), and the error block is (J + i S)/8. The second cross block is obtained by entrywise dividing the target minus this error by the first block. In the symmetric and antisymmetric bases the cross blocks have eigenvalues (1, i/2) and (1, -i). Adjoining identity diagonal blocks realizes them as calibrated Grams.

The flat input gives the lower bound 1/4 for this example. The complete calibrated Hermitian error has operator norm 1/4, so the identity times 1/4 is a matching trace-norm dual majorant. These matrix identities were checked exactly; the example is not a formalized counterexample for the four-fibre model.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.matrixUnit_row_square_le`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_improved_one_party_native_diamond`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_quarter_plaquette_native_diamond`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_sharp_zero_plaquette_native_diamond`
- Dependency: [D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond](PrincipalPlaquettePhaseDiamond.md)
- Dependency: [D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond](PrincipalTrianglePhaseDiamond.md)
