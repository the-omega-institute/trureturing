using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extreme endpoints reduce unique containing cuts to classical avoidance counts.",
        H("RotationAvoidanceEndpoints"),
        Blocks(
            Node("rotationavoidanceendpoints-ascending-extreme-endpoint-count", "Ascending count with extreme endpoints", "ascending_extreme_endpoint_count", "For width at least two, permutations of one through width plus two beginning with one and ending with width plus two, and containing 1234 in exactly the uncut rotation, number 2^(width + 1) minus twice width minus two minus the binomial coefficient choosing three from width plus one. Increasing relabelling identifies the interior with the classical class avoiding 123 and 3412, with its decreasing permutation removed.", DescribeRole.Theorem),
            Node("rotationavoidanceendpoints-fibonacci-extreme-endpoint-count", "The 1324 count with extreme endpoints", "fibonacci_extreme_endpoint_count", "For width at least two, permutations of one through width plus two beginning with one and ending with width plus two, and containing 1324 in exactly the uncut rotation, number 2^(width - 1) minus one. Increasing relabelling identifies the interior with permutations avoiding 132 and 213, with its increasing permutation removed.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
