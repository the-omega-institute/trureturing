# Sparse quartet products and fast-ratio rigidity

## Abstract

Actual unordered products with summable reciprocal multiplicity mass and their reflection rigidity.

**Theorem 1.1 (A summable coefficient budget).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.coefficient_norm_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.coefficient_norm_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary I, Data I contains real beta strictly between zero and one, positive gamma, natural multiplicities m, and summability of m/gamma. On the dependent slot type consisting of i, a Fin(m(i)) copy, and one of four roots, the negative reciprocal-root coefficients have summable norms with total at most four times the reciprocal multiplicity mass. The lower bound gamma(i) on each root norm supplies the majorant. This budget is consumed by actual_product_hasProd and actual_product_analytic.

**Theorem 1.2 (The actual quartet product converges).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_hasProd`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_hasProd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex z the actual unordered product over i of C(beta(i),gamma(i),z) raised to m(i) has product equal to the unordered linear product over slots. Polynomial factorization identifies each finite fiber with its quartet power; Mathlib HasProd.sigma assembles them without a nonvanishing hypothesis. This includes evaluations at roots. The analytic and real-axis paths consume it.

**Theorem 1.3 (Entire, normalized and reflected).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual quartet factors are multipliable at every complex point. Their product is entire, equals one at both zero and one, is unchanged by z mapped to 1-z, and for every positive epsilon obeys a whole-plane A*exp(epsilon*norm(z)) bound with A at least one. The summable-linear-product supplier proves the analytic growth. Both the real product analysis and difference_analytic use this result.

**Theorem 1.4 (Real positivity and sublinear logarithm).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_real`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x the real factors are multipliable and their real product casts to the complex product at x. On x at least one this real product is at least one, and its logarithm divided by x tends to zero. Positivity of the polynomial real-factor formula and the analytic exponential bounds prove the limit. The fast-ratio theorem uses the resulting eventual positivity and logarithmic limits.

**Theorem 1.5 (The reflected product difference).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.difference_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.difference_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary index types I and J, Data S,T, and complex b, exp(b)*S.product-T.product is entire, reflection invariant and of zero exponential type, with growth constants at least one. Its live consumer reflected_difference_zero applies the separate zero exponential type rigidity supplier.

**Theorem 1.6 (A vanishing difference is zero everywhere).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.reflected_difference_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.reflected_difference_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If that product difference tends to zero along the full positive real ray, then it is the zero function. The proof combines difference_analytic with the reflection and zero-limit supplier. This is consumed in fast_ratio_rigidity after the exponential error is multiplied by a sufficiently small growth bound.

**Theorem 1.7 (Exponential ratio error forces product equality).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.fast_ratio_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.fast_ratio_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex a,b, nonnegative real Cerr and positive real c, assume eventually for real x that the norm of exp(a*x+b)*S.product(x)/T.product(x)-1 is at most Cerr*exp(-c*x). Then a=0, exp(b)=1 and S.product=T.product. The full eventual real exponential error is retained. Positive subexponential ratios first remove a; multiplying the error by T with growth exponent c/2 makes the reflected difference vanish. Normalization at zero yields exp(b)=1 without choosing b=0.

The roots are beta plus or minus i*gamma and 1-beta plus or minus i*gamma, with repetitions retained when beta=1/2. The index types are arbitrary and multiplicities may be zero, including all zero; no distinct-root condition is used. The normalized quartic C and its real-axis formula are finite polynomial algebra, combined here with the three analytic suppliers. The scope is finite reciprocal-multiplicity mass, a sparse divisor regime. The actual zeta zero divisor is not sparse under this reciprocal summability hypothesis, so this unit proves no actual-zeta rigidity or RH statement. No minimal-type or literature-novelty claim is made. All retained helpers serve the displayed proof path; general algebraic and analytic proofs do not fall in the four computational utility classes, so utility is none.

## References

- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_analytic`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_hasProd`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_real`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.coefficient_norm_budget`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.difference_analytic`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.fast_ratio_rigidity`
- Truth anchor: `D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.reflected_difference_zero`
- Dependency: [D5/S3/Analytic/Asymptotics/PositiveSubexponentialRatio](../Asymptotics/PositiveSubexponentialRatio.md)
- Dependency: [D5/S3/Analytic/CanonicalProducts/SummableLinearProduct](SummableLinearProduct.md)
- Dependency: [D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity](../Entire/ZeroExponentialTypeRigidity.md)
