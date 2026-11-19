using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class FiveLevelTiltDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Existence of a matching tilt",
        H("Existence of a matching tilt"),
        Blocks(Describe.Lean(
            DescribeId.Create("matching-residual-zero"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/FiveLevelTilt.exists_matchingResidual_zero"),
            H("Existence of a matching tilt"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The derivative has a unique interior zero for each witness weight in the prescribed interval. Continuity and endpoint signs then give a zero of the residual equation."))),
            DescribeRole.Theorem))));
}
