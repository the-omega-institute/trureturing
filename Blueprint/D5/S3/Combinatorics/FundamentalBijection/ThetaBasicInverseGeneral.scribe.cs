using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaBasicInverseGeneralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive marked positions partition a word into intervals.",
        H("Partition into Marked Intervals"),
        Blocks(
            Node("fundamental-bijection-thetabasicinversegeneral-nextboundary", "The next marked boundary", "nextBoundary",
                "Given a predicate on positions, a length n, and a starting position s below n, the next boundary is the least larger position that satisfies the predicate or equals n; for s at least n it is n.", DescribeRole.Definition),
            Node("fundamental-bijection-thetabasicinversegeneral-filter-interval-partition", "Concatenation of consecutive intervals", "filter_interval_partition",
                "If s is a marked position or the end of a word, concatenating the intervals from each marked position at least s to the next marked boundary recovers the suffix beginning at s.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
