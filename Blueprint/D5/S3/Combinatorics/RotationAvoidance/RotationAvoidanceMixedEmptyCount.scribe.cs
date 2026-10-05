using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceMixedEmptyCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed endpoint class with empty lower interval has a binomial count.",
        H("RotationAvoidanceMixedEmptyCount"),
        Blocks(
            Node("rotationavoidancemixedemptycount-mixed-empty-lower-endpoint-count", "Mixed count with empty lower interval", "mixed_empty_lower_endpoint_count", "For last greater than two and less than size, permutations of one through size beginning with one and ending with last, and containing 1243 in exactly the uncut rotation, number the binomial coefficient choosing last minus two from size minus two, plus (size - last), minus two. The normal form combines a shuffle of decreasing intervals with the remaining split cases.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
