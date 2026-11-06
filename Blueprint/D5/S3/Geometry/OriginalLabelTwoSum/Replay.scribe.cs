// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Replay.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Replay"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Replay"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Replay"),
        Blocks(
            Node("parentof", "parentOf", "parentOf",
                "Phi applied to the literal deletion and raw link of a child. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("replaypair", "replayPair", "replayPair",
                "One child pair, on its actual native ambient, produces a finite native parent sequence. Its source and target are computed Phi states. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("replaysequence", "replaySequence", "replaySequence",
                "Entire native child list, with exact Gamma or actual no-vertical alternative. The optional no-vertical case cannot manufacture a missing Gamma. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("orderedpair", "orderedPair", "orderedPair",
                "The ordered native pair datum. It is a projection of the existing `CollapsePair`; no competing pair engine is introduced. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("orderedpairs", "orderedPairs", "orderedPairs",
                "Extract lower and upper faces from the actual native Sequence in constructor order. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("orderedpairs_cast", "orderedPairs_cast", "orderedPairs_cast",
                "Original-label source declaration consumed by the native compiler and row construction. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("orderedpairs_append", "orderedPairs_append", "orderedPairs_append",
                "Original-label source declaration consumed by the native compiler and row construction. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("rightgammapairs", "rightGammaPairs", "rightGammaPairs",
                "The right-hand Gamma chosen by the existing Prop-valued permission. This is a source constituent, not the list of a parent/replay output. Nonempty loses the identity of a supplied witness, so we expose the actual choice explicitly. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("replayfacepairs", "replayFacePairs", "replayFacePairs",
                "Replay specified solely on original lower/upper faces and a right Gamma list. No native pair, previous certificate or target sequence is re-extracted. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("replaybranchpairs", "replayBranchPairs", "replayBranchPairs",
                "This is the actual branch schedule for one child pair: the descending deletion rectangle, the descending link rectangle, the supplied Gamma schedule after lifting, or the excluded branch. Every nonempty branch is independently specified from the original pair and finite schedule data. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Definition),
            Node("replaypair_orderedpairs", "replayPair_orderedPairs", "replayPair_orderedPairs",
                "Ordered pair extraction for the three actual replay constructors. The proof is by the branch split already used by `replayPair`; `pairs_cast` removes endpoint transports, `rectangle_order` discharges the two finite descending enumerations, and `liftFibre_pairs` discharges Gamma. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem),
            Node("replaysequence_orderedpairs", "replaySequence_orderedPairs", "replaySequence_orderedPairs",
                "The complete replay list is a flat map on the ORIGINAL child faces. The right Gamma is the same classical choice as in the constructor. Membership is used only for the real head/tail pairs in the no-vertical alternative. SOURCE_ONLY_UNCOMPILED; the complete statement and ambient telescope use FromLean. Emit and catalog resolution remain open.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
