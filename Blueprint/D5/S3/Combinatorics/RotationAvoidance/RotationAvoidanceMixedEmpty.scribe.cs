using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceMixedEmptyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "When the lower block is empty, the mixed pattern has a rigid filtered form or a single split parameter.",
        H("RotationAvoidanceMixedEmpty"),
        Blocks(
            Node("rotationavoidancemixedempty-mixedemptylowernormalform", "Mixed empty lower normal form", "mixed_empty_lower_normal_form", "Let a permutation begin with one and end with last, with last greater than one. If exactly the uncut rotation contains 1243, then last is greater than two and below size. The entries below last in the interior form the reverse interval from two through last minus one. Either the upper filtered list is the interval above last and the interior is not the concatenation of that upper interval with the lower reverse interval, or there is a split between one and size minus last that gives the interior as an upper interval, the lower reverse interval, and a final upper interval.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

