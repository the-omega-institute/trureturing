using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceSlicesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint slices for 1324 have a binary factor and an odd-indexed Fibonacci factor.",
        H("RotationAvoidanceSlices"),
        Blocks(
            Node("rotationavoidanceslices-fibonacci-least-endpoint-count", "The 1324 count beginning with the minimum", "fibonacci_least_endpoint_count", "For last at least four and at most size, permutations of one through size beginning with one and ending with last, and containing 1324 in exactly the uncut rotation, number (2^(last - 3) - 1) times a factor equal to one when last equals size and to F_(2(size - last) - 1) otherwise. Increasing relabelling preserves containment and separates the classical binary middle factor from the Fibonacci upper factor.", DescribeRole.Theorem),
            Node("rotationavoidanceslices-fibonacci-endpoint-extremality", "An extreme endpoint is necessary for 1324", "fibonacci_endpoint_extremality", "For size at least four, a permutation beginning with first and ending with last that contains 1324 in exactly the uncut rotation must have first equal to one or last equal to size.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
