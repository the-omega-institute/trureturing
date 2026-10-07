using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceAscendingSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingSplit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonextreme ascending endpoints are enumerated by permutations with one ascent.",
        H("RotationAvoidanceAscendingSplit"),
        Blocks(
            Node("rotationavoidanceascendingsplit-ascending-nonextreme-endpoint-count", "Ascending count with nonextreme endpoints", "ascending_nonextreme_endpoint_count", "Let first be positive, first plus two be less than last, and last be at most size, with first greater than one or last less than size. Permutations of one through size beginning with first and ending with last, and containing 1234 in exactly the uncut rotation, number 2^(last - first - 1) minus (last - first - 1) minus one. The fixed outside blocks leave a middle permutation with exactly one ascent.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
