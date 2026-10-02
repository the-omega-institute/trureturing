using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMaximumInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMaximumInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size n at least four with maximum second. In the suffix after its first two entries, values above its first entry a decrease, and no value below a has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least two, and p is neither P(floor(n/2)) nor E(floor(n/2)). If k is even choose rank a minus k/2 plus one; otherwise choose rank n minus (k-1)/2 plus one. Increase all values at least that rank and insert it before the minimum. The result is a simple permutation in C with maximum second, minimum at position k + 1, and outside the same two families. Deleting the inserted entry and standardizing recovers p.",
        H("Insertion before the minimum when the maximum is second"),
        Blocks(
            Node("pop-stack-popstackmaximuminsertion-maximum-second-insertion", "Insertion before the minimum when the maximum is second", "maximum_second_insertion",
                "Let p be a permutation of size n at least four with maximum second. In the suffix after its first two entries, values above its first entry a decrease, and no value below a has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least two, and p is neither P(floor(n/2)) nor E(floor(n/2)). If k is even choose rank a minus k/2 plus one; otherwise choose rank n minus (k-1)/2 plus one. Increase all values at least that rank and insert it before the minimum. The result is a simple permutation in C with maximum second, minimum at position k + 1, and outside the same two families. Deleting the inserted entry and standardizing recovers p.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
