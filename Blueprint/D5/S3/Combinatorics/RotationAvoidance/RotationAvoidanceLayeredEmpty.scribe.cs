using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceLayeredEmptyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A layered endpoint class beginning at the minimum has one interval split and a Fibonacci factor.",
        H("RotationAvoidanceLayeredEmpty"),
        Blocks(
            Node("rotationavoidancelayeredempty-layered-empty-lower-endpoint-count", "Layered count with empty lower interval", "layered_empty_lower_endpoint_count", "For last greater than two and less than size, permutations of one through size beginning with one and ending with last, and containing 1423 in exactly the uncut rotation, number (last - 2) times F_(2(size - last) - 1). The middle interval has last minus two possible splits, while increasing relabelling identifies the upper factor with the classical Fibonacci avoidance class.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
