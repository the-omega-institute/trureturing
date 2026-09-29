using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeLastCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gap data and a Catalan order reconstruct an avoider with a prescribed final-cycle length.",
        H("The Final-Cycle Bijection"),
        Blocks(
            Node("arrow-thirty-two-stratum", "Final-cycle strata", "Stratum",
                "The stratum at n and k consists of avoiders on 1 through n plus one with exactly k letters after the largest value.", DescribeRole.Definition),
            Node("arrow-thirty-two-cycle-orders", "Admissible selected-letter orders", "CycleOrders",
                "An admissible order permutes a chosen list, ends in a largest letter of that list, and avoids 132.", DescribeRole.Definition),
            Node("arrow-thirty-two-join-last", "Joining the last cycle", "joinLastCycle",
                "Place n plus one between the closed-edge prefix of a gap datum and an admissible order of its selected letters. The resulting avoider lies in the stratum with that final-cycle length.", DescribeRole.Definition),
            Node("arrow-thirty-two-last-bijective", "Unique final-cycle decomposition", "joinLastCycle_bijective",
                "For every n and k, joining gap data with admissible orders is a bijection onto avoiders with k plus one letters after their largest value.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
