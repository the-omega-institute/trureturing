using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class RadiusFourDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact masks and integer weights for the fixed-SRL radius-four geometric process.",
        H("Radius-Four Certificate Data"),
        Blocks(Describe.Lean(
            DescribeId.Create("hard-core-radius-four-rows"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourData.radiusFourRows"),
            H("A lossless finite geometric presentation"),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The expanded rows contain a geometric mask and a positive integer weight. The low forty-one bits store the mask; the remaining quotient indexes repeated weights. Distinct geometric states remain distinct even when their weights agree. The companion certificate checks the decoded objects against the geometric update and verifies every integer row inequality."))),
            DescribeRole.Definition)))));
}
