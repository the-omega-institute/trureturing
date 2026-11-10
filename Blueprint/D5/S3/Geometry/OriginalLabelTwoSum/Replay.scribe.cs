using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Replay.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Replay",
            "Actual child free pairs are classified and replayed by the original rectangular or Gamma rules.",
            "original-label-two-sum-replay",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.List.Forall2")),
        H("Replay"),
        Blocks(
            Node("parentof", "parentOf", "parentOf",
                "Phi applied to the literal deletion and raw link of a child. ", DescribeRole.Definition),
            Node("replaypair", "replayPair", "replayPair",
                "One child pair, on its actual native ambient, produces a finite native parent sequence. Its source and target are computed Phi states. ", DescribeRole.Definition),
            Node("replaysequence", "replaySequence", "replaySequence",
                "Entire native child list, with exact Gamma or actual no-vertical alternative. The optional no-vertical case cannot manufacture a missing Gamma. ", DescribeRole.Definition),
            Node("orderedpair", "orderedPair", "orderedPair",
                "The ordered native pair datum. It is a projection of the existing `CollapsePair`; no competing pair engine is introduced. ", DescribeRole.Definition),
            Node("orderedpairs", "orderedPairs", "orderedPairs",
                "Extract lower and upper faces from the actual native Sequence in constructor order. ", DescribeRole.Definition),
            Node("orderedpairs-cast", "orderedPairs_cast", "orderedPairs_cast",
                "Original-label source declaration consumed by the native compiler and row construction. ", DescribeRole.Theorem),
            Node("orderedpairs-append", "orderedPairs_append", "orderedPairs_append",
                "Original-label source declaration consumed by the native compiler and row construction. ", DescribeRole.Theorem),
            Node("rightgammapairs", "rightGammaPairs", "rightGammaPairs",
                "The right-hand Gamma chosen by the existing Prop-valued permission. This is a source constituent, not the list of a parent/replay output. Nonempty loses the identity of a supplied witness, so we expose the actual choice explicitly. ", DescribeRole.Definition),
            Node("replayfacepairs", "replayFacePairs", "replayFacePairs",
                "Replay specified solely on original lower/upper faces and a right Gamma list. No native pair, previous certificate or target sequence is re-extracted. ", DescribeRole.Definition),
            Node("replaybranchpairs", "replayBranchPairs", "replayBranchPairs",
                "This is the actual branch schedule for one child pair: the descending deletion rectangle, the descending link rectangle, the supplied Gamma schedule after lifting, or the excluded branch. Every nonempty branch is independently specified from the original pair and finite schedule data. ", DescribeRole.Definition),
            Node("replaypair-orderedpairs", "replayPair_orderedPairs", "replayPair_orderedPairs",
                "Ordered pair extraction for the three actual replay constructors. The proof is by the branch split already used by `replayPair`; `pairs_cast` removes endpoint transports, `rectangle_order` discharges the two finite descending enumerations, and `liftFibre_pairs` discharges Gamma. ", DescribeRole.Theorem),
            Node("replaysequence-orderedpairs", "replaySequence_orderedPairs", "replaySequence_orderedPairs",
                "The complete replay list is a flat map on the ORIGINAL child faces. The right Gamma is the same classical choice as in the constructor. Membership is used only for the real head/tail pairs in the no-vertical alternative. ", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
