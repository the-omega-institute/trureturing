using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class DiamondBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completely positive domination on every reference",
        H("Completely positive domination on every reference"),
        Blocks(Describe.Lean(
            DescribeId.Create("amplified-majorant-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DiamondBounds.amplified_traceNorm_le_of_completelyPositive_majorant"),
            H("Completely positive domination on every reference"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A completely positive majorant of a trace-annihilating map controls its trace norm by twice the trace mass. Hermitian block dilation extends the inequality to arbitrary complex inputs."))),
            DescribeRole.Theorem))));
}
