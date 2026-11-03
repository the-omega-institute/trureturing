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
                DescribeId.Create("finite-current-regular-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicFinitePrincipalParts.finite_current_regular_coeff"),
                H("finite_current_regular_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive regular index, the entire finite-current tail equals the original pairScalar, including equal input and output indices."))), DescribeRole.Theorem),
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
