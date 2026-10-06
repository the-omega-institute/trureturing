using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceBinaryContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive endpoint contraction relates circular avoidance to cyclic pattern avoidance and enumerates the resulting binary family.",
        H("RotationAvoidanceBinaryContraction"),
        Blocks(
            Node("rotationavoidancebinarycontraction-consecutiveendpointcontraction", "Consecutive endpoint contraction", "consecutive_endpoint_contraction", "For a permutation whose first entry is first and whose last entry is first plus one, and for either pattern 2413 or 1342, all rotations contain the pattern only at the uncut position exactly when the interior with the final entry avoids every cyclic rotation of the pattern and the uncut word contains the pattern.", DescribeRole.Theorem),
            Node("rotationavoidancebinarycontraction-binaryleastconsecutiveendpointcount", "Binary count for consecutive endpoints", "binary_least_consecutive_endpoint_count", "For width at least three, the number of permutations of one through width plus two that begin with one, end with two, and have 1342 in exactly the uncut rotation is 2 to the width minus width minus one. Increasing relabelling preserves containment and identifies the contracted interior with a classical avoidance class.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

