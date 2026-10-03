using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let q be a permutation in C of size at least four with minimum in its second position, and let p be obtained by deleting that minimum and subtracting one from every remaining entry. Then p is a permutation in C, and shifting its values up by one and reinserting the minimum recovers q. The permutation q is simple if and only if p is simple with minimum not in the second position, or p is the first-entry decreasing inflation of a simple skeleton in C of size at least four, or p equals B at its size.",
        H("Deleting a minimum in the second position"),
        Blocks(
            Node("pop-stack-popstackdecomposition-minimum-two-decomposition", "Deleting a minimum in the second position", "minimum_two_decomposition",
                "Let q be a permutation in C of size at least four with minimum in its second position, and let p be obtained by deleting that minimum and subtracting one from every remaining entry. Then p is a permutation in C, and shifting its values up by one and reinserting the minimum recovers q. The permutation q is simple if and only if p is simple with minimum not in the second position, or p is the first-entry decreasing inflation of a simple skeleton in C of size at least four, or p equals B at its size.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
