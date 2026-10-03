using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripExpansionCancellationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A color-preserving involution cancels the signed weights of all gap tuples except those with paired colors in the even-indexed gaps.",
        H("Sign-Reversing Cancellation of Colored Gaps"),
        Blocks(
            Node("cigler-strip-expansion-cancellation-gap-involution", "The first-defect gap transformation", "gapInvolution",
                "Inspect successive pairs consisting of an even-indexed gap and the following odd-indexed gap, with indices starting at zero. If the even gap has even length and the odd gap is empty, leave both in place and continue. If the even gap has even length and the odd gap is nonempty, move the first color of the odd gap to the end of the even gap. If the even gap has odd length, move its last color to the start of the odd gap. Stop after the first move. Lists with fewer than two gaps remain unchanged.", DescribeRole.Definition),
            Node("cigler-strip-expansion-cancellation-fixed-gaps", "The fixed gap condition", "FixedGaps",
                "A colored gap tuple is fixed when, for every consecutive pair of gaps starting at an even index, the even-indexed gap has even length and the following odd-indexed gap is empty. Indices start at zero. A final unpaired gap is unrestricted, and a list with at most one gap satisfies the condition.", DescribeRole.Definition),
            Node("cigler-strip-expansion-cancellation-colored-gap-involution", "Color-preserving sign reversal", "colored_gap_involution",
                "For every colored gap tuple, the gap transformation preserves both the number of gaps and their concatenated color sequence, and applying it twice returns the original tuple. Its fixed points are exactly the tuples satisfying the fixed gap condition, which have zero odd-gap charge. Every non-fixed tuple has the negative of the sign of its image, with sign (-1)^q for odd-gap charge q. There also exists an involution on Boolean pair sequences preserving their length, extracted skeleton and concatenated gap colors, whose fixed points have exactly the fixed gap condition. It preserves the Motzkin strip condition for every natural bound, and negates the signed Motzkin weight starting at height zero of every non-fixed path in that strip.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
