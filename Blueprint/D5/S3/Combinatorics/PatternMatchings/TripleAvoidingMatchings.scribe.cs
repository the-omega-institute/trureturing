using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Catalan-Fibonacci series gives the generating function of all perfect matchings avoiding 123, 132 and 213.",
        H("The generating function for matchings avoiding 123, 132 and 213"),
        Blocks(
            Node("bss-result", "The perfect-matching enumeration", "result",
                "Let a_n count the perfect matchings on 2n ordered vertices avoiding P1 = {123, 132, 213}, with three-arc occurrences requiring all three left endpoints to precede all three right endpoints and with labels complementary to right-endpoint order. Put A(z) = sum a_n z^n and H(z) = sum Cat_k F_{k+3} z^k over nonnegative integers. Then (1-z-zH(z))A(z) = 1-zH(z), equivalently A(z) = (1-zH(z))/(1-z-zH(z)). This enumerates the P1 clause of Section 6, Question 1 of Biswas, Shankar and Sivasubramanian. The identity holds as a formal power series with integer coefficients and includes the empty matching.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("biswas-shankar-sivasubramanian-p1-matchings"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
