// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class ParentFibresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/ParentFibres.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/ParentFibres"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/ParentFibres"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("ParentFibres"),
        Blocks(
            Node("criticalpart", "criticalPart", "criticalPart",
                "These are literal X-parts; the removed label e is not an output coordinate. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("localwindow", "localWindow", "localWindow",
                "These are literal X-parts; the removed label e is not an output coordinate. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("localbase", "localBase", "localBase",
                "These are literal X-parts; the removed label e is not an output coordinate. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("parent_fibre_base", "parent_fibre_base", "parent_fibre_base",
                "Boundary and fibre-intersection facts for the COMPUTED Cbase. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("parent_fibre_cross", "parent_fibre_cross", "parent_fibre_cross",
                "Exact cross-fibre exclusion. The one direction that can intersect is the second-kind fibre into a first-kind block, and its right part then lies in Z. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("parent_initial_fibres", "parent_initial_fibres", "parent_initial_fibres",
                "The initial fibre decomposition is PROVED from proper-boundary membership, not assumed as an endpoint or desired parent row equation. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
