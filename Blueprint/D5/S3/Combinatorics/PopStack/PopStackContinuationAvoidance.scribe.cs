using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackContinuationAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackContinuationAvoidance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size n at least two in C whose second entry is less than n and whose first entry is not one more than its second. Then W(p) belongs to C. If n is at least four and p is simple, W(p) is a simple permutation of size n + 1.",
        H("Avoidance under ordinary continuation"),
        Blocks(
            Node("pop-stack-popstackcontinuationavoidance-ordinary-continuation", "Avoidance under ordinary continuation", "ordinary_continuation",
                "Let p be a permutation of size n at least two in C whose second entry is less than n and whose first entry is not one more than its second. Then W(p) belongs to C. If n is at least four and p is simple, W(p) is a simple permutation of size n + 1.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
