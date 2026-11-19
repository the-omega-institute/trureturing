using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ProtocolScoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Score bound for deterministic projective trees",
        H("Score bound for deterministic projective trees"),
        Blocks(Describe.Lean(
            DescribeId.Create("protocol-score-le"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProtocolScore.protocol_score_le"),
            H("Score bound for deterministic projective trees"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A first nontrivial projection reduces the score problem to complementary ranks. Leading trivial measurements preserve the bound, and a single terminal unitary has the required score bound directly."))),
            DescribeRole.Theorem))));
}
