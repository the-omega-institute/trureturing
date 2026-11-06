// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class BatchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Batch.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Batch"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Batch"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Batch"),
        Blocks(
            Node("fibrelayers", "fibreLayers", "fibreLayers",
                "Literal union of indexed fibre families. Repeated indices are not needed. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("mem_fibrelayers", "mem_fibreLayers", "mem_fibreLayers",
                "Membership retains the actual fibre index and local face. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("batchfibre", "batchFibre", "batchFibre",
                "A finite batch, with actual evolving base (finished N-fibres and unfinished M-fibres). The pair list is precisely the concatenation of the lifted local lists, in the supplied finite index order. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
