using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The avoidance numbers and their ordinary generating series are defined for the arrow pattern (32; 1 to 3).",
        H("The (32; 1 to 3) Avoidance Series"),
        Blocks(
            Node("arrow-thirty-two-count", "Avoidance numbers", "count",
                "The number at n is the cardinality of the permutations of 1 through n avoiding (32; 1 to 3).",
                DescribeRole.Definition),
            Node("arrow-thirty-two-series", "Ordinary generating series", "series",
                "The coefficient of x to the n in this integer power series is the avoidance number at n.",
                DescribeRole.Definition),
            Node("arrow-thirty-two-claim", "Cubic equation and distinguished branch", "claim",
                "The avoidance series F satisfies 1 + (3x - 2)F + (1 - x)(1 - 2x)F squared + x cubed F cubed = 0. Any integer formal power series G satisfying the same equation, with constant coefficient one and coefficient of x equal to one, equals F.",
                DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
