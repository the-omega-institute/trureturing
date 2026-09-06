using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class RadiusFourDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core memory, exact path semantics and integer certificates.",
        H("Radius-Four Certificate Data"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourdata-radiusfourrows"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourData.radiusFourRows"),
                H("Lossless geometric data"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The low forty-one bits encode a blocked set; the remaining quotient indexes an integer weight. Repeated weights do not identify distinct geometric states. The companion source checks the actual decoded geometry and every row."))),
                DescribeRole.Definition))));
}
