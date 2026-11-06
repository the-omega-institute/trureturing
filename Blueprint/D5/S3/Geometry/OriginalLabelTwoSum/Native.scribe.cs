// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class NativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Native.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Native"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Native"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Native"),
        Blocks(
            Node("cut", "cut", "cut",
                "Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("cut_empty", "cut_empty", "cut_empty",
                "Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("cut_cut", "cut_cut", "cut_cut",
                "Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("emitpair", "emitPair", "emitPair",
                "Populate the actual native pair, using the whole current raw family. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("emitpair_retained", "emitPair_retained", "emitPair_retained",
                "The equality is literal deletion of the upper ideal of the lower face. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("fibrebefore", "fibreBefore", "fibreBefore",
                "Label-order tie break. The finite enumeration is fixed once per ambient Fintype instance; cardinality is always the primary comparison. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("fibres", "fibres", "fibres",
                "Actual terminating merge-sort, not an assumed fibre schedule. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("fibres_spec", "fibres_spec", "fibres_spec",
                "Actual terminating merge-sort, not an assumed fibre schedule. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("rectangle", "rectangle", "rectangle",
                "Public rectangle endpoint and genuine ordered native list. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("rectangle_order", "rectangle_order", "rectangle_order",
                "The list statement refers to the real pair extraction, and contains no external pair schedule assumption. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("cut_fixed", "cut_fixed", "cut_fixed",
                "Fixed coordinate consequence of the EXISTING Sequence homotopy. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
