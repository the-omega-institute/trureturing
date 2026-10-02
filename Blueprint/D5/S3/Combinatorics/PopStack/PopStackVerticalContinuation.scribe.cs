using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackVerticalContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a word p of length n, undoV(p) equals P(floor(n/2)) if p = E(floor(n/2)), and equals E(floor(n/2)-1) if p = P(floor(n/2)). Otherwise, if the second entry is below n, delete the first entry and decrease each remaining value greater than it. In the remaining case delete the entry immediately before the minimum and decrease each remaining value larger than the deleted entry. Subtraction is truncated at zero.",
        H("Reverse vertical continuation"),
        Blocks(
            Node("pop-stack-popstackverticalcontinuation-augmented", "The augmented simple class", "augmented",
                "For each nonnegative n, augmented(n) consists of the simple permutations of size n in C, together with E(floor(n/2)) when n is odd and at least three.", DescribeRole.Definition),
            Node("pop-stack-popstackverticalcontinuation-v", "Vertical continuation", "V",
                "For a word p of length n, V(p) equals E(floor(n/2)) if p = P(floor(n/2)). If p = E(floor(n/2)), insert the rank floor((n+3)/2) at the end after increasing every value at least that rank. Otherwise, if the second entry is less than n, use W(p). In the remaining case let k be the zero-based position of one and choose rank a minus k/2 plus one when k is even, or n minus (k-1)/2 plus one when k is odd, where a is the first entry. Increase every value at least that rank and insert it immediately before the minimum.", DescribeRole.Definition),
            Node("pop-stack-popstackverticalcontinuation-undov", "Reverse vertical continuation", "undoV",
                "For a word p of length n, undoV(p) equals P(floor(n/2)) if p = E(floor(n/2)), and equals E(floor(n/2)-1) if p = P(floor(n/2)). Otherwise, if the second entry is below n, delete the first entry and decrease each remaining value greater than it. In the remaining case delete the entry immediately before the minimum and decrease each remaining value larger than the deleted entry. Subtraction is truncated at zero.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
