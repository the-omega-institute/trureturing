# Fixed row and column orders

## Abstract

Exact parameter degrees of the original fixed elimination determinants

The coefficient ring is Z[b] and the outer polynomial variable is the original independent r. sourcePolynomial has entries E01, E02 and E12, in that order. For k:Fin 2, sylvesterRow consists of r^14 E01 through E01 followed by r^14 E(k+1) through E(k+1). literalSylvester retains these thirty rows in columns r^29 through 1. actualResultant(k) is exactly its determinant, so k=0 denotes the source R1 and k=1 denotes R2. In the formulas, sourcePair(b,0)=sourceE1(b) and sourcePair(b,1)=sourceE2(b), and resultantEvaluation(b,p) evaluates the integer polynomial p at the real parameter b.

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

A common real root z supplies the nonzero vector (z^29,...,1) to each corresponding thirty-row matrix. Its determinant therefore vanishes, including at specialized degree drops. For the twenty-eight original rows, the fixed-minor relation transports through coefficient evaluation to the actual integer determinant polynomials. These two implications give the following source-level result.

**Theorem 1.4 (Critical sources satisfy the original elimination equations).**

$$\forall t, b\in \mathbb{R}, \operatorname{M}(0, 1, t, b)= 0\land \operatorname{M}(0, 2, t, b)= 0\land \operatorname{M}(1, 2, t, b)= 0\implies \operatorname{sourceD}(t, b)= 0\lor ((\forall k\in \operatorname{Fin}(2), \operatorname{resultantEvaluation}(b, \operatorname{actualResultant}(k))= 0)\land tb\operatorname{evalB}(b, \operatorname{actualMinorA0}())+ \operatorname{evalB}(b, \operatorname{actualMinorC0}())= 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.source_critical_literal_elimination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t,b, let M(i,j,t,b)=sourceBt(i,t,b) sourceBb(j,t,b)-sourceBb(i,t,b) sourceBt(j,t,b). If all three ordered minors vanish, then either D(t,b)=0 or both actual fixed resultants vanish at b and the actual fixed linear minors satisfy (t b) a0(b)+c0(b)=0. The three division-free normalization identities supply the common source roots; the E12 identity supplies the second resultant. The singular branch is explicit, so the statement retains b=0, all real parameters and all leading-degree drops. It gives necessary elimination equations, without asserting that a projected resultant root lifts to a critical source.

These are polynomial bounds and exact degrees before specialization. All rows, columns and zero padding remain fixed even when specialization lowers a leading degree. These results do not prove exact resultant or minor factorizations, the displayed common factors, primitive positive normalization, coprimality, or any root or world exhaustion.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_elimination_exact_degrees`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_degree_bounds`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_degree_bound`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralSylvesterBounds.source_critical_literal_elimination`
- Dependency: [D5/S3/Observer/CubicGain/LiteralElimination](LiteralElimination.md)
- Dependency: [D5/S3/Observer/CubicGain/LiteralLeadingCertificates](LiteralLeadingCertificates.md)
