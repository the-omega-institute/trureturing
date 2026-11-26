using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ScoreReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measured Choi score of a protocol",
        H("Measured Choi score of a protocol"),
        Blocks(Describe.Lean(
            DescribeId.Create("measured-protocol-score"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ScoreReadout.measuredScore_protocolMap_le"),
            H("Measured Choi score of a protocol"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The measured score is the sum of squared flag-weighted Kraus traces. Terminal normalization and the complete projective-tree bound limit that score uniformly."))),
            DescribeRole.Theorem))));
}
