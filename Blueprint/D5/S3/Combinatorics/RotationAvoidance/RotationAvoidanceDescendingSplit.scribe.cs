using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceDescendingSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingSplit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated endpoints for 1432 leave an upper interval with one ascent.",
        H("RotationAvoidanceDescendingSplit"),
        Blocks(
            Node("rotationavoidancedescendingsplit-descending-positive-middle-endpoint-count", "Descending count with separated endpoints", "descending_positive_middle_endpoint_count", "Let first be positive, first plus one be less than last, and last plus two be at most size. Permutations of one through size beginning with first and ending with last, and containing 1432 in exactly the uncut rotation, number 2^(size - last) minus (size - last) minus one. The normal form reduces the choice to two decreasing upper blocks whose concatenation has exactly one ascent.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
