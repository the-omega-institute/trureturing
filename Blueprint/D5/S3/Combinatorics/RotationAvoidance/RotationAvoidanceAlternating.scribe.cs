using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceAlternatingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternating.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated endpoint intervals give a product of two odd-indexed Fibonacci numbers.",
        H("RotationAvoidanceAlternating"),
        Blocks(
            Node("rotationavoidancealternating-alternating-positive-middle-endpoint-count", "Alternating count with separated endpoints", "alternating_positive_middle_endpoint_count", "Let first be at least two, first plus one be less than last, and last be less than size. Among permutations of one through size beginning with first and ending with last, those containing 2413 in exactly the uncut rotation number F_(2(size - last) - 1) times F_(2(first - 1) - 1). The separated lower and upper factors are classical avoidance classes; increasing relabelling preserves pattern containment, and each factor is counted by the odd-indexed Fibonacci enumeration.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
