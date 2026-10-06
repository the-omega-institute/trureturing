using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceLayeredDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The layered endpoint case decomposes into four blocks with order and avoidance constraints.",
        H("RotationAvoidanceLayered"),
        Blocks(
            Node("rotationavoidancelayered-layeredendpointnormalform", "Layered endpoint normal form", "layered_endpoint_normal_form", "Let a permutation begin with first, end with last, and have first less than last. If exactly the uncut rotation contains 1423, then first plus one is less than last and last is below size. The interior splits into before, upper, lower and suffix blocks: upper and lower are permutations of the values above last and below first, while before with suffix contains the middle values. Both outer blocks are decreasing, every suffix value is below every before value, the suffix is nonempty, and if first is at least two then before is empty. The upper block avoids 312 and 2314, and the lower block avoids 231 and 1423.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

