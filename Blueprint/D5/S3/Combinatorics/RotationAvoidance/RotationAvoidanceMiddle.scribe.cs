using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceMiddleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated endpoints for 2143 force a five-block increasing normal form.",
        H("RotationAvoidanceMiddle"),
        Blocks(
            Node("rotationavoidancemiddle-paired-endpoint-middle-normal-form", "Five-block normal form for separated endpoints", "paired_endpoint_middle_normal_form", "Let size be at least four and first plus one be less than last. If first followed by interior followed by last permutes one through size and contains 2143 in exactly the uncut rotation, there exist lowerSplit and upperSplit with one at most lowerSplit less than first and upperSplit less than size minus last. The interior concatenates five increasing intervals: the first upperSplit entries above last, the first lowerSplit positive entries, every entry strictly between first and last, the remaining entries above last, and the remaining entries below first.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
