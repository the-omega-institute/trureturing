using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class RankThreeTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Score bound on complementary ranks three and two",
        H("Score bound on complementary ranks three and two"),
        Blocks(Describe.Lean(
            DescribeId.Create("rank-three-two-cp-score-le"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/RankThreeTwo.rank_three_two_cp_score_le"),
            H("Score bound on complementary ranks three and two"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Spectator-adapted support frames give the opposing sector inequalities. The two compressed continuation scores are bounded by the common tilted objective."))),
            DescribeRole.Theorem))));
}
