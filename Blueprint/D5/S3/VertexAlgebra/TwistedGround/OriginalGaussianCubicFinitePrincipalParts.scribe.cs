using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianCubicFinitePrincipalPartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Cubic Finite Principal Parts",
        H("Original Gaussian Cubic Finite Principal Parts"),
        Blocks(
            Paragraph(Text("Finite binomial numerators determine the principal parts of the original current. The literal TT and UT kernels have degree-dependent pole bounds at all indices, with the original square-root equation retained for external roots.")),
            Paragraph(Text("These sources are an implementation checkpoint. Native verification and independent admission review are separate requirements; no official acceptance or physical realization is asserted. Full four-halfmode geometry, two-source transport, identityK crossing, Monster moonshine, VOA/CFT/anomaly/fusion, complete string theory and AdS/CFT remain unfinished.")),
            Describe.Lean(
                DescribeId.Create("finite-current-numerator-degree"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_degree"),
                H("finite_current_numerator_degree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual truncation polynomial for the current has degree strictly below s+1; this degree supplier is consumed by finite numerator uniqueness."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-current-negative-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_negative_coeff"),
                H("finite_current_negative_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every negative Laurent exponent, the current has exactly the prescribed principal coefficient, including the totalized s=0 case."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-current-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_residue"),
                H("finite_current_residue"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite current Laurent series has zero residue at exponent minus one for every natural index."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-current-regular-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_regular_coeff"),
                H("finite_current_regular_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive regular index, the entire finite-current tail equals the original pairScalar, including equal input and output indices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("currentrow-eq-finite-numerator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.currentRow_eq_finite_numerator"),
                H("currentRow_eq_finite_numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation of the explicit finite numerator gives the unchanged original currentRow, with arbitrary complex external scalar and totalized b=0."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-current-numerator-unique"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_numerator_unique"),
                H("finite_current_numerator_unique"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An arbitrary polynomial of the stated strict degree is forced to the constructed numerator by its truncated half-series product."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-root-exclusions"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.external_root_exclusions"),
                H("external_root_exclusions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original root equation alone forces a nonzero root and excludes b=-1; no square-root convention is selected."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-polar-derivative-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_polar_derivative_identity"),
                H("literal_polar_derivative_identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the literal cubic derivative numerator and identify it with the independently defined polar polynomial."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-diagonal-polynomials"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_diagonal_polynomials"),
                H("literal_diagonal_polynomials"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the literal polar and cubic at a=b+v, retaining the full polynomial coefficients without a finite testing cutoff."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-pullback-polar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.literal_pullback_polar"),
                H("literal_pullback_polar"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After multiplication by u squared, the literal rational substitution a=x/u gives the original pulled-back polar when u is nonzero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-tt-pole-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_tt_pole_bound"),
                H("cubic_tt_pole_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every permitted modulus degree and negative mode, the actual TT coefficient vanishes under the original bound d<=s."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-ut-pole-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_pole_bound"),
                H("cubic_ut_pole_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every permitted modulus degree and negative mode, the actual UT coefficient vanishes under the original strict bound d<s."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-ut-degree-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.cubic_ut_degree_zero"),
                H("cubic_ut_degree_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compute the actual degree-zero UT power-series coefficient directly from the original kernel and scalar constant term."))), DescribeRole.Theorem))));
}
