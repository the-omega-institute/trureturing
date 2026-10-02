using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackLeftDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackLeftDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size at least three with minimum in its second position. Prepend two after increasing every other value than one by one. The result is simple if and only if every proper nontrivial interval of p is its second and third entries with values one and two. The result is both simple and in C if and only if exactly one of the following holds: p itself is simple and in C; or p is the second-entry inflation by 12 of a unique simple skeleton in C whose minimum is second and whose length is two or at least four.",
        H("Simplicity after prepending two"),
        Blocks(
            Node("pop-stack-popstackleftdecomposition-prepend-two-decomposition", "Simplicity after prepending two", "prepend_two_decomposition",
                "Let p be a permutation of size at least three with minimum in its second position. Prepend two after increasing every other value than one by one. The result is simple if and only if every proper nontrivial interval of p is its second and third entries with values one and two. The result is both simple and in C if and only if exactly one of the following holds: p itself is simple and in C; or p is the second-entry inflation by 12 of a unique simple skeleton in C whose minimum is second and whose length is two or at least four.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
