using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteLexSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteLexSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite lexicographic rank descent",
        H("Finite lexicographic rank descent"),
        Blocks(
            Paragraph(Text("The finite coordinate and value orders give a natural rank on complete events. A checked actual pivot and every earlier coordinate establish strict descent for every compatible completion.")),
            Node("act", "act", "Act on a whole event",
                "The coordinate equivalence and common value equivalence act on every event coordinate.", DescribeRole.Definition),
            Node("dominates", "dominates", "Check an actual first decrease",
                "The pivot values must be assigned and strictly decrease. Each earlier coordinate must be fixed by the whole action or have assigned equal values.", DescribeRole.Definition),
            Node("rank", "rank", "Rank the complete lexicographic event",
                "The finite lexicographic order is transported to a natural index.", DescribeRole.Definition),
            Node("dominates-rank-lt", "dominates_rank_lt", "Every compatible completion strictly decreases",
                "The checked pivot and all earlier equalities give a strict lexicographic inequality and therefore strict natural-rank descent.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
