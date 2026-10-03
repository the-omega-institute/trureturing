using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMaximumDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMaximumDeletion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size at least five with maximum second. In the suffix after its first two entries, values above the first entry decrease, and no value below the first entry has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least three, and p is neither P(floor(n/2)) nor E(floor(n/2)), where n is its length. Delete the entry immediately before the minimum and standardize. The predecessor is a simple permutation in C with maximum second and minimum at position k minus one, and remains outside those two families. Inserting before its minimum the rank prescribed by the parity of that position recovers p.",
        H("Deletion before the minimum when the maximum is second"),
        Blocks(
            Node("pop-stack-popstackmaximumdeletion-maximum-second-deletion", "Deletion before the minimum when the maximum is second", "maximum_second_deletion",
                "Let p be a permutation of size at least five with maximum second. In the suffix after its first two entries, values above the first entry decrease, and no value below the first entry has both a smaller and a larger such value later. Assume no adjacent entries have consecutive values, the minimum has zero-based position k at least three, and p is neither P(floor(n/2)) nor E(floor(n/2)), where n is its length. Delete the entry immediately before the minimum and standardize. The predecessor is a simple permutation in C with maximum second and minimum at position k minus one, and remains outside those two families. Inserting before its minimum the rank prescribed by the parity of that position recovers p.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
