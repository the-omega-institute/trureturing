using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackContinuationReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackContinuationReflection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let q be a simple permutation in C whose minimum has position k at least three and whose second entry is below its maximum. Delete the first entry and decrease each remaining value larger than the deleted value. The resulting permutation p is simple, belongs to C, has its minimum at position k minus one, has its second entry below its maximum, and satisfies W(p) = q. Positions are numbered from zero.",
        H("Deleting the first entry of an ordinary continuation"),
        Blocks(
            Node("pop-stack-popstackcontinuationreflection-ordinary-continuation-inverse", "Deleting the first entry of an ordinary continuation", "ordinary_continuation_inverse",
                "Let q be a simple permutation in C whose minimum has position k at least three and whose second entry is below its maximum. Delete the first entry and decrease each remaining value larger than the deleted value. The resulting permutation p is simple, belongs to C, has its minimum at position k minus one, has its second entry below its maximum, and satisfies W(p) = q. Positions are numbered from zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
