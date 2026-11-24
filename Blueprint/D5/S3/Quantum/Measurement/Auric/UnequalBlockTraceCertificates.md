# Direct and complementary entropy for strictly admissible traces

## Abstract

Strict-trace certificates for unequal rank caps

**Theorem 1.1 (Direct weights for strictly admissible traces).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_direct_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_direct_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Gale (1957). *A theorem on flows in networks*. DOI: [10.2140/pjm.1957.7.1073](https://doi.org/10.2140/pjm.1957.7.1073). URL: <https://msp.org/pjm/1957/7-2/p04.xhtml>.

*Commentary.*

Let ℓⱼ = max(d − mⱼ, 0) and b = d − ∑ⱼ ℓⱼ, with ∑ⱼ ℓⱼ ≤ d. Assume ∑ⱼ τⱼ = d and 0 < τⱼ < d − ℓⱼ = min(d, mⱼ) for every row j. There are positive weights wⱼ summing to one whose masked proportional allocation has multiplicity-weighted row masses τⱼ in the original labels. This uses ℓᵢ copies of the column missing row i and b copies of the common column.

For each column take the log of the sum of exp(uⱼ) over the allowed rows, where u is the vector of row prices. Sum these potentials with the column multiplicities and subtract ∑ⱼ τⱼuⱼ. The objective is invariant under adding a common constant to the prices. Testing the allowed vertices bounds it below by the price spread times the minimum strict row slack, the minimum of τⱼ and d − ℓⱼ − τⱼ over all rows. Fixing one price at zero makes the sublevel through the zero vector compact, so the continuous objective attains a global minimum.

At the minimum the coordinate derivatives vanish. Each column derivative is the corresponding masked softmax entry. Normalizing exp(uⱼ) over all rows gives w, and the derivative equations give the prescribed row masses. The denominators stay positive even for a column type of multiplicity zero.

**Theorem 1.2 (Direct spectral maximum for strictly admissible traces).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_direct`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_direct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite matrix carrier of dimension d, assume ∑ⱼ ℓⱼ ≤ d, ∑ⱼ τⱼ = d and 0 < τⱼ < d − ℓⱼ for each original label j. Sort the positive direct weights in nonincreasing order and permute the caps, traces and missing types with them. The ordered direct maximum gives diagonal attainment and an upper bound. Inverting the row permutation preserves the spectral sum and transports each cap and trace back to its original effect.

The greatest value is the direct allocation value with the permuted deficits, the common multiplicity b and the sorted weights. The feasible spectral-value set uses the original caps and traces. A zero multiplicity gives an empty diagonal block.

**Theorem 1.3 (Clipped weights and scales for strictly admissible traces).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_complement_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_complement_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same strict row trace and dimension conditions, there are positive row weights wⱼ and positive column scales k_c. The allowed entry is max(0, 1 − wⱼk_c), and the excluded entry is zero. All four formal columns sum to one, including those of multiplicity zero. The multiplicity-weighted row masses equal τⱼ in the original labels.

At prices u take wⱼ = exp(−uⱼ). For a missing type the scale is the reciprocal of the sum of the two allowed weights. For the common type, write S for the sum of all weights and M for their maximum. The scale is max(2/S, 1/(S − M)). This formula keeps the clipped allocation continuous through the cutoff. A common-column entry can vanish even under strict row trace inequalities.

The column potential is the maximum over its allowed probability simplex of the complementary entropy plus the linear price term. The scalar supporting inequalities establish this maximum at the clipped allocation, and evaluating at a vertex yields the price lower bound used in compact minimization. Comparing scores at the minimizing prices and at nearby prices on either side of each coordinate gives the two opposite inequalities for the displaced row mass. Continuity gives equality with τⱼ at the minimum.

**Theorem 1.4 (Complementary spectral maximum for strictly admissible traces).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same strict trace hypotheses on a finite matrix carrier, sort the positive row weights in nondecreasing order. The induced permutation of missing types makes their reciprocal scales nondecreasing. The common scale is at least every missing scale, so the ordered complementary maximum applies after relabeling. The induced column permutation fixes the common type and preserves each block multiplicity with its type.

The greatest value is the clipped allocation value for the permuted deficits, the common multiplicity and the transported weights and scales. Inverting the row permutation recovers exactly the original labeled feasible spectral-value set. These maxima concern the three effects and their spectra under strict trace inequalities.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_complement_certificate`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_direct_certificate`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_complement`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates.exists_isGreatest_direct`
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects](UnequalBlockEffects.md)
