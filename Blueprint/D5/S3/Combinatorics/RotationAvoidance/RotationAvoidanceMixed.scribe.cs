using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceMixedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed pattern with a nonempty lower part forces adjacent endpoints and has a binomial enumeration.",
        H("RotationAvoidanceMixed"),
        Blocks(
            Node("rotationavoidancemixed-mixednonemptylowernormalform", "Mixed nonempty lower normal form", "mixed_nonempty_lower_normal_form", "Let a permutation begin with first, end with last, and have first at least two and first less than last. If exactly the uncut rotation contains 1243, then last equals first plus two and is below size. The interior begins with first plus one, followed by a list whose values are exactly those below first or above last. The lower filtered subsequence is decreasing and the upper filtered subsequence is increasing.", DescribeRole.Theorem),
            Node("rotationavoidancemixed-mixednonemptylowerendpointcount", "Mixed nonempty lower endpoint enumeration", "mixed_nonempty_lower_endpoint_count", "For first at least two and first plus two below size, the number of permutations of one through size that begin with first, end with first plus two, and have 1243 in exactly the uncut rotation is the binomial coefficient choosing first minus one from size minus three.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

