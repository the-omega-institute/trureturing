using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedThreeFieldCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-variable coefficient indices", H("Three-variable coefficient indices"), Blocks(
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-signed-cleared-collision"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_cleared_collision"),
                H("signed_cleared_collision"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a genuinely lower-supported ordered channel, the all-integer Borcherds transform has finite support and equals the legally substituted native common series at every signed exponent. In the negative collision region, the positive integer binomial kernel has finite degree and all remaining terms vanish by the native numerator support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-slice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice"),
                H("slice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a signed spectator coefficient in a generally infinite three-variable native series, using zero extension when necessary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-slice-extend"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice_extend"),
                H("slice_extend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Native slicing and signed zero extension give the same coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-cross"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.cross"),
                H("cross"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two finite binomial fibers expand the spectator cross factors of the three-field clearing polynomial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-clearing-three"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.clearing_three"),
                H("clearing_three"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three-variable pair clearing equals the bivariate clearing of the finite spectator cross-factor expansion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-innerarguments"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerArguments"),
                H("innerArguments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The legal partial triangular coordinates are z0, t+z2, z2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-innercollision"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision"),
                H("innerCollision"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Substitute the partial triangular coordinates into the generally infinite native series."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-innercollision-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_coeff"),
                H("innerCollision_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A coefficient of the partial triangular substitution is a finite antidiagonal binomial sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-innercollision-signed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_signed"),
                H("innerCollision_signed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native inner substitution agrees with the bivariate collision on every signed spectator and collision exponent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedthreefieldcollision-signed-transform-clear"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_transform_clear"),
                H("signed_transform_clear"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite signed binomial transform passes through polynomial clearing by the binomial-series composition law. Both sums use the same actual lower support cutoff."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("index3"),
                DeclarationHandle.Create(Prefix + "index3"),
                H("index3"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native index with the three indicated nonnegative coordinates."))), DescribeRole.Definition))));
}
