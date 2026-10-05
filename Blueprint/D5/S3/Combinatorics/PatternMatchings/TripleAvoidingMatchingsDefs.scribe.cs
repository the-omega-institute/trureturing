using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perfect matchings avoiding three patterns are counted by an ordinary generating function in the number of arcs.",
        H("Perfect matchings and the Catalan-Fibonacci generating function"),
        Blocks(
            Node("bss-defs-matching", "Perfect matchings", "Matching",
                "A perfect matching on 2n ordered vertices is a fixed-point-free involution of the vertices numbered from zero through 2n-1. Each orbit of size two is an arc. The empty matching is included.", DescribeRole.Definition),
            Node("bss-defs-finite-matchings", "The finite family of perfect matchings", "instFintypeMatching",
                "For each nonnegative integer n, the perfect matchings on 2n ordered vertices form a finite family. An enumeration of this family permits counting those matchings that satisfy pattern avoidance.", DescribeRole.Definition),
            Node("bss-defs-occurs", "Three-arc pattern occurrences", "Occurs",
                "An occurrence chooses three increasing left endpoints, all preceding every chosen right endpoint. For each pair of chosen arcs, the order of the right endpoints is opposite to the order of their pattern labels. Thus 123 labels three nested arcs and 321 labels three mutually crossing arcs.", DescribeRole.Definition),
            Node("bss-defs-p1", "The three forbidden patterns", "P1",
                "The pattern set P1 consists of 123, 132 and 213, represented by the zero-based label sequences (0,1,2), (0,2,1) and (1,0,2).", DescribeRole.Definition),
            Node("bss-defs-avoidsp1", "Avoidance of the pattern set", "AvoidsP1",
                "A matching avoids P1 when none of its three-arc selections is an occurrence of 123, 132 or 213 under the right-endpoint convention just specified.", DescribeRole.Definition),
            Node("bss-defs-a", "The number of avoiding matchings", "a",
                "For each nonnegative integer n, a_n is the number of perfect matchings on 2n ordered vertices that avoid P1. Matchings are distinguished by their pairs of vertices.", DescribeRole.Definition),
            Node("bss-defs-aseries", "The matching generating function", "aSeries",
                "A(z) is the formal power series with integer coefficients whose coefficient of z^n is a_n. The variable counts arcs rather than individual vertices.", DescribeRole.Definition),
            Node("bss-defs-hseries", "The Catalan-Fibonacci series", "hSeries",
                "H(z) is the sum over nonnegative integers k of Cat_k F_{k+3} z^k, where Cat_k is the kth Catalan number and F_0 = 0, F_1 = 1 are the Fibonacci initial values.", DescribeRole.Definition),
            Node("bss-defs-claim", "The enumeration identity", "claim",
                "The enumeration asserts (1-z-zH(z))A(z) = 1-zH(z) in the ring of formal power series with integer coefficients. Since 1-z-zH(z) has constant coefficient one, this is equivalent to A(z) = (1-zH(z))/(1-z-zH(z)).", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
