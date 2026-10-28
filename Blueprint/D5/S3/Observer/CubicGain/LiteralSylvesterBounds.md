# Fixed row and column orders

## Abstract

Exact parameter degrees of the original fixed elimination determinants

The coefficient ring is Z[b] and the outer polynomial variable is the original independent r. sourcePolynomial has entries E01, E02 and E12, in that order. For k:Fin 2, sylvesterRow consists of r^14 E01 through E01 followed by r^14 E(k+1) through E(k+1). literalSylvester retains these thirty rows in columns r^29 through 1. actualResultant(k) is exactly its determinant, so k=0 denotes the source R1 and k=1 denotes R2.

Every source coefficient of r^j has b degree at most 17-j when nonzero. A row shifted by s and a column of exponent c therefore have nonzero entry degree plus c at most 17+s. Every nonzero permutation product uses every column once. Summing these inequalities gives the degree bound for each determinant term and hence the determinant. Zero entries and zero determinant terms are included.

**Theorem 1.1 (Both original fixed resultants have degree at most 285).**

$$\forall k\in \operatorname{Fin}(2), \operatorname{natDegree}(\operatorname{actualResultant}(k))\leq 285$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_degree_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k:Fin 2, actualResultant(k) has natural degree at most 285. The row weights are 17 plus shifts 14 through 0, twice; the column weights are 29 through 0. No assumption requires a leading coefficient to remain nonzero at any parameter value.

The original fixed linear minors are actualMinorA0 and actualMinorC0 of ActualMinorLift. They retain rows r^13 E01 through E01 followed by r^13 E02 through E02. Their first twenty-seven columns are r^28 through r^2; their final columns are respectively r and 1, with no sign or scale adjustment.

**Theorem 1.2 (The original fixed linear-minor degree bounds).**

$$\operatorname{natDegree}(a_{0})\leq 252\land \operatorname{natDegree}(c_{0})\leq 253$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_degree_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural degrees of actualMinorA0 and actualMinorC0 are at most 252 and 253 respectively. The same weighted argument uses shifts 13 through 0 twice and the original retained column exponents.

**Theorem 1.3 (Exact degrees of the original fixed determinants).**

$$(\forall k\in \operatorname{Fin}(2), \operatorname{natDegree}(\operatorname{actualResultant}(k))= 285)\land \operatorname{natDegree}(a_{0})= 252\land \operatorname{natDegree}(c_{0})= 253$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_elimination_exact_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both original fixed Sylvester determinants have natural degree 285; the original r-column and constant-column minors have natural degrees 252 and 253 respectively. For each entry the proof extracts the coefficient at row weight minus column exponent. Scaling rows and columns by powers of X identifies the determinant coefficient with the determinant of this integer leading matrix. The exact full-matrix certificates in LiteralLeadingCertificates prove that all four leading determinants are nonzero. Every coefficient array is checked against sourcePolynomial, and every matrix entry is connected to the original fixed rows and columns.

**Theorem 1.4 (A literal fixed-degree resultant vanishes at every common source root).**

$$\forall b, z, k\in \operatorname{Fin}(2), {\operatorname{eval}(z\operatorname{sourceE0}(b))}= 0\land {\operatorname{eval}(z\operatorname{sourcePair}(bk))}= 0\implies \operatorname{resultantEvaluation}(b\operatorname{actualResultant}(k))= 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_vanishes_of_common_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either original pair, a common real source root supplies the nonzero vector (z^29,...,1) to the exact thirty-row fixed Sylvester matrix. The determinant therefore vanishes after evaluating the parameter b, even when a specialized leading coefficient drops. The theorem uses the original E0/E1/E2 coefficient arrays and does not select a root or divide by a leading coefficient.

**Theorem 1.5 (The literal fixed linear minors obey the common-root relation).**

$$\forall b, z, {\operatorname{eval}(z\operatorname{sourceE0}(b))}= 0\land {\operatorname{eval}(z\operatorname{sourceE1}(b))}= 0\implies z \operatorname{evalB}(b\operatorname{actualMinorA0}())+ \operatorname{evalB}(b\operatorname{actualMinorC0}())= 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_relation_of_common_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common real root of the original E0 and E1 rows gives z times the evaluated r-column determinant plus the evaluated constant-column determinant equal to zero. The proof transports the existing 28-row fixed-minor relation through the integer coefficient determinants, retaining every row and column and dividing by no leading coefficient.

These are polynomial bounds and exact degrees before specialization. All rows, columns and zero padding remain fixed even when specialization lowers a leading degree. These results do not prove exact resultant or minor factorizations, the displayed common factors, primitive positive normalization, coprimality, or any root or world exhaustion.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_elimination_exact_degrees`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_degree_bounds`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_relation_of_common_root`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_degree_bound`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_vanishes_of_common_root`
- Dependency: [D5/S3/Observer/CubicGain/LiteralElimination](LiteralElimination.md)
- Dependency: [D5/S3/Observer/CubicGain/LiteralLeadingCertificates](LiteralLeadingCertificates.md)
