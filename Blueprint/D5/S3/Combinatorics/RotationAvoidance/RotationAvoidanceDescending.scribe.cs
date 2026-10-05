using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceDescendingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The descending consecutive endpoint case has a filtered normal form and an explicit enumeration.",
        H("RotationAvoidanceDescending"),
        Blocks(
            Node("rotationavoidancedescending-descendingconsecutiveendpointnormalform", "Descending consecutive endpoint normal form", "descending_consecutive_endpoint_normal_form", "Let a permutation begin with first and end with first plus one. If first is positive and exactly the uncut rotation contains 1432, then first plus three is at most the size. The interior consists of the entries above first plus one, in their original order, followed by the decreasing list of entries below first. The upper filtered list is a permutation of its full interval, avoids 321 and 2143, and is not strictly increasing.", DescribeRole.Theorem),
            Node("rotationavoidancedescending-descendingconsecutiveendpointcount", "Descending consecutive endpoint enumeration", "descending_consecutive_endpoint_count", "For positive first with first plus three at most size, the number of permutations of one through size that begin with first, end with first plus one, and have 1432 in exactly the uncut rotation equals 2 to the power size minus first, minus twice size minus first minus one, minus two, minus the binomial coefficient choosing three from size minus first. Increasing relabelling and reversal identify the upper interval with the classical class avoiding 123 and 3412, after removing its decreasing permutation.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

