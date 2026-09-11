using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class AdaptiveRadiusFourDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact adaptive radius-four masks, local orders and integer potentials.",
        H("Adaptive radius-four data"),
        Blocks(Describe.Lean(
            DescribeId.Create("adaptive-radius-four-data"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourData.radiusFourRows"),
            H("Lossless geometric data"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every row represents an actual blocked vertex set, an integer upper potential and a selected local ordering. Storage sharing does not identify mathematical states. The companion certificate checks the full selected geometric closure and all integer potential inequalities."))),
            DescribeRole.Definition))));
}
