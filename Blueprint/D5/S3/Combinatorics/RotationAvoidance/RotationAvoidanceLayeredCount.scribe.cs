using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceLayeredCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A layered endpoint class with nonempty lower interval has a Fibonacci product count.",
        H("RotationAvoidanceLayeredCount"),
        Blocks(
            Node("rotationavoidancelayeredcount-layered-nonempty-lower-endpoint-count", "Layered count with nonempty lower interval", "layered_nonempty_lower_endpoint_count", "Let first be at least two, first plus one be less than last, and last be less than size. Permutations of one through size beginning with first and ending with last, and containing 1423 in exactly the uncut rotation, number F_(2(size - last) - 1) times F_(2(first - 1) - 1). The lower and upper factors are classical avoidance classes. Complementing the lower interval and increasing relabelling of the upper interval reduce both factors to the odd-indexed Fibonacci enumeration.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
