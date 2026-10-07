using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.OddIndependence;

internal sealed class OddGridDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OddIndependence/OddGrid.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/caro2025oddindependencegrids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent square-grid sets above density three eighths with correction four divided by the side length contain a full four-neighbour cross.",
        H("An affirmative answer to the square-grid full-cross question"),
        Blocks(
            Node("odd-grid-result", "A vanishing correction forces a full cross", "result",
                "Problem 29 of Caro, Petrusevski, Skrekovski and Tuza has an affirmative answer. Take epsilon(n)=4/n for positive n and epsilon(0)=0. This real sequence tends to zero. For every n at least one, an independent set S of the n by n square grid with cardinality at least (3/8 + 4/n)n squared contains all four neighbours of an interior vertex. Indeed, if S contains no full cross, translate it by two and fill the remaining array positions with zeros. The local discharge inequality and ninefold window counting yield 8 times the cardinality of S at most 3(n+2) squared. But (3/8 + 4/n)n squared is strictly greater than 3(n+2) squared divided by eight for every n at least one, giving a contradiction. A full cross in the padded array translates back to four distinct neighbours of an interior grid vertex, and every neighbour of that vertex belongs to S.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("caro-petrusevski-skrekovski-tuza-grid-three-eighths"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
