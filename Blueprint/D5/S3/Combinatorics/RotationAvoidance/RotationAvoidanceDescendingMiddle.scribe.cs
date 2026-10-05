using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceDescendingMiddleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A descending pattern with a separated middle endpoint yields increasing upper pieces and a lower suffix.",
        H("RotationAvoidanceDescendingMiddle"),
        Blocks(
            Node("rotationavoidancedescendingmiddle-descendingpositivemiddlenormalform", "Descending positive middle normal form", "descending_positive_middle_normal_form", "Let a permutation begin with first, end with last, and have first plus one less than last. If exactly the uncut rotation contains 1432, then last plus two is at most size. The interior is an increasing list of upper values, followed by the consecutive middle interval, followed by a suffix and the increasing list of values below first. The upper list and suffix together contain all values above last, each of the two displayed outer pieces is increasing, and some upper value exceeds some lower value in the suffix.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

