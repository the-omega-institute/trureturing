using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceAlternatingContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive endpoint contraction counts alternating words by a Fibonacci difference.",
        H("RotationAvoidanceAlternatingContraction"),
        Blocks(
            Node("rotationavoidancealternatingcontraction-alternating-consecutive-endpoint-count", "Alternating count with consecutive endpoints", "alternating_consecutive_endpoint_count", "For width at least three and pivot at least two but less than width plus one, permutations of one through width plus two beginning with pivot and ending with pivot plus one, and containing 2413 in exactly the uncut rotation, number F_(2 width - 1) minus F_(2(pivot - 1) - 1) times F_(2(width + 1 - pivot) - 1). Contraction and its increasing inverse relabelling preserve classical containment. The count subtracts the separated circular avoidance class from the full contracted circular class.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
