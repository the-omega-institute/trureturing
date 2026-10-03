using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualSpineCarryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The offset spine belongs to one finite actual Cloitre split tree and preserves its scalar carry total.",
        H("Actual Cloitre Spine and Scalar Carry"),
        Blocks(
            Paragraph(Text(
                "All conclusions use the original actual sequence C, selector g, orbit X "
                + "and complete conditional Hyp21_1 bundle. No inhabitant of that bundle "
                + "is established. G is the natural golden floor reading.")),
            Node("actualTree", "The complete actual ordered tree",
                "Zero gives the exterior empty tree. Labels one and two are terminal nodes. "
                + "Every label n at least three has ordered children g(n) and n-g(n), "
                + "each expanded by its own actual selector. Unconditional actual_foundations "
                + "makes both children positive and strictly smaller, proving finiteness."),
            Node("rootLabel", "Root labels", "The empty tree has exterior label zero."),
            Node("subtreeAt", "Subtree occurrences",
                "A list of Boolean sides identifies one complete subtree occurrence. "
                + "False means left and true means right; a missing path returns none. "
                + "Equal labels at different addresses remain distinct occurrences."),
            Node("totalCarry", "Structural scalar carry fold",
                "A terminal label contributes zero. At each internal node, add the scalar "
                + "Beatty deficit of its ordered child labels and both recursive child totals. "
                + "This is an actual internal-node fold, not a definition by root defect. "
                + "The Beatty deficit normalizes to G(a)+G(b)-G(a+b)."),
            Node("threshold", "Width-dependent endpoint threshold", "K(t)=12*t+7."),
            Node("retainedBit", "The ordered offset child",
                "Retain the left child at even F(j-1)+t-1 and the right child at odd parity."),
            Node("stepSize", "Rank decrement", "The corresponding decrement is one or two."),
            Node("anchorRank", "The opposite anchor rank",
                "The sibling anchor has rank j-2 in the even branch and j-1 in the odd branch."),
            Node("rank", "Successive ranks",
                "Iterate j to j-stepSize(t,j), keeping the numerical width t fixed."),
            Node("address", "Successive occurrence addresses",
                "Start at the empty root address and append the retained Boolean side."),
            Node("SplitFacts", "Complete actual split facts",
                "The ordered children have exactly the offset and anchor labels. Current "
                + "and retained defects equal h(t)=t-G(t); the anchor defect and scalar "
                + "split carry are zero. For t at least two, only the retained child has "
                + "positive defect. At t=1 both defects vanish and the offset label selects it."),
            Node("CongruenceControl", "Six rank transitions",
                "For odd t and j modulo three equal to 0,1,2, the decrements are 2,1,2 "
                + "and successor residues are 1,0,0. For even t they are 1,2,1 and 2,2,1. "
                + "Reduce the full successor rank j-r modulo three, not truncated residues."),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-full22-2"),
                DeclarationHandle.Create(Prefix + "full22_2"),
                H("One actual finite spine conserves scalar carry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under every U satisfying the unchanged Hyp21_1, the structural "
                        + "fold on every positive actual tree equals its canonical root defect. "
                        + "For t at least one and k at least K(t), every active rank j >= K(t) "
                        + "has the complete ordered split facts and six congruence transitions. "
                        + "There is a positive finite first stopping index L, all earlier "
                        + "ranks are active, and J=rank(t,k,L) is K(t)-1 or K(t)-2.")),
                    Paragraph(Text(
                        "For each natural 0 <= i <= L, address t k i identifies the complete "
                        + "actualTree (F (rank t k i) + t) inside the one root actualTree (F k + t). "
                        + "For each natural 0 <= i < L, the opposite address "
                        + "address t k i ++ [!(retainedBit t (rank t k i))] identifies its complete "
                        + "Fibonacci anchor tree actualTree (F (anchorRank t (rank t k i))); "
                        + "that anchor's totalCarry is zero, and "
                        + "totalCarry (actualTree (F (rank t k i) + t)) = "
                        + "totalCarry (actualTree (F (rank t k (i + 1)) + t)). "
                        + "Expanding the folds along these actual "
                        + "occurrences preserves the root total through the terminal tree, "
                        + "whose persistent defect and total are h(t). The separated digit "
                        + "supplier is used down to K(t)-2, without an endpoint hypothesis "
                        + "at that terminal rank.")),
                    Paragraph(Text(
                        "Scalar zero does not assert zero unit-bit carry or zero at every "
                        + "internal node of an anchor subtree. The six control states retain "
                        + "the numerical width, do not bound it, do not classify the terminal "
                        + "tree and do not establish global selector regularity. Composition "
                        + "and unit-direction tree identities are outside this theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Invariants/CloitreActualRightProfile")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Tower/GoldenGapZeckendorf")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Deficit/ZeckendorfDisplacementReading")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/GoldenPhaseDeficit")),
        ]));

    private static DocumentBlock.Describe Node(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("cloitre-spine-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
