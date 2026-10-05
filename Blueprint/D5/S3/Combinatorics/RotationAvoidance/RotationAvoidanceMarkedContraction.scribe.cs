using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceMarkedContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMarkedContraction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contraction of the endpoints two and three gives a binary exponential count.",
        H("RotationAvoidanceMarkedContraction"),
        Blocks(
            Node("rotationavoidancemarkedcontraction-binary-second-consecutive-endpoint-count", "Binary count with endpoints two and three", "binary_second_consecutive_endpoint_count", "For width at least three, permutations of one through width plus two beginning with two and ending with three, and containing 1342 in exactly the uncut rotation, number 2^width minus twice width. Contraction and its increasing inverse relabelling preserve pattern containment and identify the relevant circular classes with classical avoidance classes.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
