using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class WellFoundedRankCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/WellFoundedRankCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every well-founded dependency relation has a canonical strict ordinal rank coordinate.",
        H("Well-Founded Rank Coordinate"),
        Blocks(Describe.Lean(
            DescribeId.Create("well-founded-rank-is-strict"),
            DeclarationHandle.Create(Prefix + "dependencyRank_strict"),
            H("Canonical well-founded rank is strict"),
            StatementSource.FromAuthor(RankFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a well-founded dependency relation, assign each node the ordinal rank of "
                        + "its accessibility proof. Every direct dependency edge strictly "
                        + "increases this canonical rank.")),
                Paragraph(Text(
                    "The well-foundedness premise is explicit. The theorem packages strictness as "
                        + "StrictDependencyCoordinate and does not claim the rank map is "
                        + "injective."))),
            DescribeRole.Theorem))));

    private static Formula RankFormula()
    {
        Formula edge = F.Id("edge");
        Formula wellFounded = F.Id("wellFounded");

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"),
            Comma, RowBreak, Grp(),
            Forall, Sp, wellFounded, Colon, Sp, Call("WellFounded", edge), Comma,
            RowBreak, Grp(),
            Call("StrictDependencyCoordinate", edge, Call("dependencyRank", wellFounded)), Dot));
    }
}
