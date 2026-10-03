using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerCycleWalkTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted words give transfer matrix powers, and pairing Dyck steps relates signed strip sums to a path with endpoint loops.",
        H("Transfer Matrices for Signed Strip Paths"),
        Blocks(
            Node("cigler-cycle-walk-transfer-word-contribution", "The contribution of a labeled word", "wordContribution",
                "Given a set of states, a label alphabet, a transition function and an integer weight for each state and label, the contribution of a word from a starting state to a target is the product of its successive transition weights if its final state is the target, and zero otherwise. The empty word contributes one when the starting state is the target and zero otherwise.", DescribeRole.Definition),
            Node("cigler-cycle-walk-transfer-weighted-walks-eq-pow", "Weighted words and matrix powers", "weighted_walks_eq_pow",
                "For finite state and label sets, let T(s, t) be the sum of the weights of labels that send s to t. For every natural number r and every pair of states s and t, the sum of word contributions over all label sequences of length r starting at s and ending at t equals T^r(s, t). Transition weights are arbitrary integers, and distinct labels with the same destination contribute separately to the matrix entry.", DescribeRole.Theorem),
            Node("cigler-cycle-walk-transfer-paired-transition", "Transitions of paired steps", "pairedTransition",
                "The states are heights zero through b minus one. A pair of up-steps raises the height by one with weight one if the new height is below b; otherwise it stays at its starting height with weight zero. A pair of down-steps lowers a positive height by one with weight minus one; at height zero it stays there with weight zero. Either mixed pair stays at height h with weight (-1)^h.", DescribeRole.Definition),
            Node("cigler-cycle-walk-transfer-paired-adj", "The paired transition matrix", "pairedAdj",
                "For a natural number b, pairedAdj is the integer matrix on the b heights whose entry from s to t sums the weights of all four ordered pairs of Boolean steps having destination t under pairedTransition. The two mixed pairs are distinct contributions, so their total diagonal weight at height h is 2(-1)^h.", DescribeRole.Definition),
            Node("cigler-cycle-walk-transfer-paired-strip-eq-pow", "The signed strip sum as a paired moment", "paired_strip_eq_pow",
                "For every positive integer b and nonnegative integer r, the signed Dyck path sum of semilength r plus one in the strip of height 2b equals the entry at (0, 0) of pairedAdj(b)^r. Removing the enclosing up-step and down-step and pairing the remaining steps gives a two-colored Motzkin excursion with r steps at heights zero through b minus one, preserving its signed weight.", DescribeRole.Theorem),
            Node("cigler-cycle-walk-transfer-folded-adj", "A path with loops at both ends", "foldedAdj",
                "For a natural number v, foldedAdj is the integer adjacency matrix on vertices zero through v minus one. Two consecutive vertices have entry one. A diagonal entry is one at vertex zero and at vertex v minus one, and all other entries are zero. When v is one there is a single loop of weight one, and when v is zero the matrix has no entries.", DescribeRole.Definition),
            Node("cigler-cycle-walk-transfer-strip-eq-folded", "The signed strip sum as a looped-path moment", "strip_eq_folded",
                "For every positive odd integer b and nonnegative integer r, the signed Dyck path sum of semilength r plus one in the strip of height 2b equals foldedAdj(b + 1)^{r+1}(0, 0). Rectangular matrices factor the paired transition matrix in one order and the looped-path adjacency matrix in the reverse order. Alternating signs cancel the interior diagonal entries, while odd b gives a loop of weight one at each endpoint.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
