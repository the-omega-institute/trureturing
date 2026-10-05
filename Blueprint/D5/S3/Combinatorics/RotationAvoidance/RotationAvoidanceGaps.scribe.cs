using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceGapsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGaps.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three strict inequalities distinguish circular classes with one containing cut.",
        H("RotationAvoidanceGaps"),
        Blocks(
            Node("rotationavoidancegaps-three-strict-count-gaps", "Three strict count comparisons", "three_strict_count_gaps", "For every size at least seven, among circular permutations rooted at one with exactly one containing rotation, the 2143 count is strictly smaller than the 1234 count, the 1234 count is strictly smaller than the 1432 count, and the 1243 count is strictly smaller than the 1342 count. Endpoint decompositions and their exact counts yield all three comparisons.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
