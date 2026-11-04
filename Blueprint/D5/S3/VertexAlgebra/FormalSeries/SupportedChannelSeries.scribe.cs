using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;
internal sealed class SupportedChannelSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SupportedChannelSeries", H("Supported collision coefficients and reconstruction"), Blocks(
            Paragraph(Text("Classical binomial-series algebra is applied to lower-supported vector coefficients. Mathlib supplies binomialSeries_add and native MvPowerSeries substitution. The finite diagonal arguments establish both the signed inverse expansion of (x-y)^N and the positive-factor inverse expansion of (y+t)^A. Native substitution has zero constant arguments; its antidiagonal coefficient fiber is finite even when the numerator has infinite support. Coefficient readouts are complex-linear and need not preserve multiplication.")),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-clear"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.clear"),
                H("clear"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-powerindex"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.powerIndex"),
                H("powerIndex"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-extend"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.extend"),
                H("extend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-binomialtransform"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.binomialTransform"),
                H("binomialTransform"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-supported-reconstruction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.supported_reconstruction"),
                H("supported_reconstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-collisionarguments"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.collisionArguments"),
                H("collisionArguments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-collision"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.collision"),
                H("collision"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-collision-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.collision_coeff"),
                H("collision_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-cleared-collision-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.cleared_collision_coeff"),
                H("cleared_collision_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-mapseries"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.mapSeries"),
                H("mapSeries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-collision-map"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.collision_map"),
                H("collision_map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-positiveclear"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.positiveClear"),
                H("positiveClear"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supportedchannelseries-supported-positive-reconstruction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries.supported_positive_reconstruction"),
                H("supported_positive_reconstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact assumptions, coefficient conventions and quantifiers are given by the Lean telescope."))),
                DescribeRole.Theorem)
        )));
}
