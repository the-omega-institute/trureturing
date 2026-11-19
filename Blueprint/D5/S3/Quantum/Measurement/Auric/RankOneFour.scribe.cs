using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class RankOneFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Score bound on complementary ranks one and four",
        H("Score bound on complementary ranks one and four"),
        Blocks(Describe.Lean(
            DescribeId.Create("rank-one-four-cp-score-le"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/RankOneFour.rank_one_four_cp_score_le"),
            H("Score bound on complementary ranks one and four"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Isometric compression and the weighted trace-square-root bound control the two branch scores for an arbitrary normalized continuation on each support."))),
            DescribeRole.Theorem))));
}
