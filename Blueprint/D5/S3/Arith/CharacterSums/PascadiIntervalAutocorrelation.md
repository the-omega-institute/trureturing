# Actual interval weights and central counts

## Abstract

Literal integer interval autocorrelations retain residue multiplicities and give the six-letter central comparison with factor 64.

Let G be a finite group, and let u and v be homomorphisms from the additive integers, written multiplicatively, into G. The interval measure sums one group-algebra atom for every integer in [-N,N]. Equal images remain separate summands; no injectivity or interval shorter than the group order is assumed. The normalized autocorrelation divides by 2N+1.

**Theorem 1.1 (The exact triangular weights).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerInterval_autocorrelation_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerInterval_autocorrelation_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual autocorrelation coefficient is the sum over integers |n|<=2N of (2N+1-|n|) times the coefficient of the atom at u(n). This sums every residue collision with its full integer multiplicity.

Expand the two interval sums and group pairs (a,b) by their integer difference n=a-b. The difference fiber is in explicit bijection with the intersection of two integer intervals, whose cardinality is 2N+1-|n|. This is an integer fiber count, not a count of distinct group images.

**Theorem 1.2 (The coefficient sandwich).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerIntervalFejer_sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerIntervalFejer_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient by coefficient, the original interval measure is at most twice its normalized autocorrelation, and the normalized autocorrelation is at most the measure on [-2N,2N]. The normalized triangular weight lies in [0,1] on its support and is at least 1/2 on [-N,N]. The argument sums these inequalities before identifying any equal images.

**Theorem 1.3 (Six alternating interval letters at a central element).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.alternating_integer_interval_center_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.alternating_integer_interval_center_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any central z in G, the coefficient at z of (mu_u,N times mu_v,M)^3 is at most 64 times the identity coefficient of (mu_u,2N times mu_v,2M)^3. N and M are separate nonnegative integer widths. No symmetry or positivity of the nonsymmetric product itself is assumed.

The lower sandwich and actual convolution monotonicity contribute the six factors of 2. The central autocorrelation theorem applies to the normalized actual factors. The upper sandwich then removes all triangular weights in the doubled intervals. The group-algebra anti-involution and Gram factor are constructed in CentralAutocorrelation; there is no assumed center-bound or positive-operator supplier.

This general interval result does not by itself identify a matrix word with its coefficient. PascadiScalarCenters supplies the exact upper/lower unipotent word, its overall sign, the row permutation, the scalar centrality proof, and the natural-floor interpretation for real widths.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.alternating_integer_interval_center_le`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerIntervalFejer_sandwich`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation.integerInterval_autocorrelation_coeff`
- Dependency: [D5/S3/FiniteGroups/RegularRepresentation/CentralAutocorrelation](../../FiniteGroups/RegularRepresentation/CentralAutocorrelation.md)
