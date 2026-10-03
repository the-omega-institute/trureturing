using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripExpansionPairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairing the interior steps of an even-strip Dyck path gives a two-colored Motzkin path with the same weight.",
        H("Pairing Dyck Steps into Motzkin Steps"),
        Blocks(
            Node("cigler-strip-expansion-pairing-expand-blocks", "Expand a sequence of pairs", "expandBlocks",
                "Expand each ordered pair of Boolean steps into its first step followed by its second step, preserving the order of all pairs. The empty sequence of pairs expands to the empty sequence of steps.", DescribeRole.Definition),
            Node("cigler-strip-expansion-pairing-pair-blocks", "Group consecutive steps into pairs", "pairBlocks",
                "Group a Boolean step sequence into consecutive ordered pairs, starting at its first step. If the sequence has odd length, its last step is discarded. A sequence of length zero or one produces no pairs.", DescribeRole.Definition),
            Node("cigler-strip-expansion-pairing-expand-path", "Enclose the expanded pairs", "expandPath",
                "Expand the sequence of pairs, prepend one up-step and append one down-step. A sequence of n pairs therefore gives a path of length 2(n + 1). An up-step is represented by true and a down-step by false.", DescribeRole.Definition),
            Node("cigler-strip-expansion-pairing-coarse-height", "The coarse prefix height", "coarseHeight",
                "The coarse height after k pairs is the sum of the first k coarse increments. A pair of two up-steps contributes one, a pair of two down-steps contributes minus one, and either mixed pair contributes zero. Taking more pairs than are present uses the entire sequence.", DescribeRole.Definition),
            Node("cigler-strip-expansion-pairing-is-motzkin-strip", "Motzkin paths in a strip", "IsMotzkinStrip",
                "For a natural number b, a sequence of pairs represents a two-colored Motzkin path in the strip of height b when every coarse prefix height lies between zero and b, inclusive, and its final coarse height is zero. The mixed pairs up-down and down-up are the two colors of horizontal step.", DescribeRole.Definition),
            Node("cigler-strip-expansion-pairing-motzkin-weight", "Ordinary and signed Motzkin weights", "motzkinWeight",
                "Starting at a natural height a, multiply the successive coarse step weights while updating the height. An up-step has weight one and increases the height by one. A down-step decreases the height by one, with subtraction truncated at zero, and has weight t in the ordinary case and minus t in the signed case. An up-down horizontal pair has weight t and a down-up pair has weight one. In the signed case each horizontal weight is additionally multiplied by (-1)^a at its current height. The empty sequence has weight one.", DescribeRole.Definition),
            Node("cigler-strip-expansion-pairing-bijection", "The even-strip pairing bijection", "pairing_bijection",
                "For every positive integer m and nonnegative integer n, Dyck paths of length 2(n + 1) in the strip of height 2m are in bijection with two-colored Motzkin paths of length n in the strip of height m minus one. Expansion of the image of any Dyck path recovers that path, and the inverse map on every Motzkin path is expansion enclosed by an initial up-step and a final down-step.", DescribeRole.Theorem),
            Node("cigler-strip-expansion-pairing-weights", "Preservation of both weights", "pairing_weights",
                "For every natural strip height b and every two-colored Motzkin path in that strip, its enclosed expansion has Narayana weight equal to its ordinary Motzkin weight starting at height zero. Its signed Narayana weight equals its signed Motzkin weight starting at height zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
