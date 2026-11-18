using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.CanonicalProducts;

internal sealed class SparseQuartetProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unordered products with summable reciprocal multiplicity mass and their reflection rigidity.", H("Sparse quartet products and fast-ratio rigidity"),
        Blocks(
            Describe.Lean(DescribeId.Create("sparse-quartet-product-coefficient-norm-budget"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.coefficient_norm_budget"),
                H("A summable coefficient budget"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary I, Data I contains real beta strictly between zero and one, positive gamma, natural multiplicities m, and summability of m/gamma. On the dependent slot type consisting of i, a Fin(m(i)) copy, and one of four roots, the negative reciprocal-root coefficients have summable norms with total at most four times the reciprocal multiplicity mass. The lower bound gamma(i) on each root norm supplies the majorant. This budget is consumed by actual_product_hasProd and actual_product_analytic."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-quartet-product-actual-product-has-prod"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_hasProd"),
                H("The actual quartet product converges"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every complex z the actual unordered product over i of C(beta(i),gamma(i),z) raised to m(i) has product equal to the unordered linear product over slots. Polynomial factorization identifies each finite fiber with its quartet power; Mathlib HasProd.sigma assembles them without a nonvanishing hypothesis. This includes evaluations at roots. The analytic and real-axis paths consume it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-quartet-product-actual-product-analytic"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_analytic"),
                H("Entire, normalized and reflected"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual quartet factors are multipliable at every complex point. Their product is entire, equals one at both zero and one, is unchanged by z mapped to 1-z, and for every positive epsilon obeys a whole-plane A*exp(epsilon*norm(z)) bound with A at least one. The summable-linear-product supplier proves the analytic growth. Both the real product analysis and difference_analytic use this result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-quartet-product-actual-product-real"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.actual_product_real"),
                H("Real positivity and sublinear logarithm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x the real factors are multipliable and their real product casts to the complex product at x. On x at least one this real product is at least one, and its logarithm divided by x tends to zero. Positivity of the polynomial real-factor formula and the analytic exponential bounds prove the limit. The fast-ratio theorem uses the resulting eventual positivity and logarithmic limits."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-quartet-product-difference-analytic"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.difference_analytic"),
                H("The reflected product difference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary index types I and J, Data S,T, and complex b, exp(b)*S.product-T.product is entire, reflection invariant and of zero exponential type, with growth constants at least one. Its live consumer reflected_difference_zero applies the separate zero exponential type rigidity supplier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-quartet-product-reflected-difference-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.reflected_difference_zero"),
                H("A vanishing difference is zero everywhere"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If that product difference tends to zero along the full positive real ray, then it is the zero function. The proof combines difference_analytic with the reflection and zero-limit supplier. This is consumed in fast_ratio_rigidity after the exponential error is multiplied by a sufficiently small growth bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-quartet-product-fast-ratio-rigidity"),
                DeclarationHandle.Create("D5/S3/Analytic/CanonicalProducts/SparseQuartetProduct.fast_ratio_rigidity"),
                H("Exponential ratio error forces product equality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary complex a,b, nonnegative real Cerr and positive real c, assume eventually for real x that the norm of exp(a*x+b)*S.product(x)/T.product(x)-1 is at most Cerr*exp(-c*x). Then a=0, exp(b)=1 and S.product=T.product. The full eventual real exponential error is retained. Positive subexponential ratios first remove a; multiplying the error by T with growth exponent c/2 makes the reflected difference vanish. Normalization at zero yields exp(b)=1 without choosing b=0."))), DescribeRole.Theorem),
            Paragraph(Text("The roots are beta plus or minus i*gamma and 1-beta plus or minus i*gamma, with repetitions retained when beta=1/2. The index types are arbitrary and multiplicities may be zero, including all zero; no distinct-root condition is used. The normalized quartic C and its real-axis formula are finite polynomial algebra, combined here with the three analytic suppliers. The scope is finite reciprocal-multiplicity mass, a sparse divisor regime. The actual zeta zero divisor is not sparse under this reciprocal summability hypothesis, so this unit proves no actual-zeta rigidity or RH statement. No minimal-type or literature-novelty claim is made. All retained helpers serve the displayed proof path; general algebraic and analytic proofs do not fall in the four computational utility classes, so utility is none.")))));
}
