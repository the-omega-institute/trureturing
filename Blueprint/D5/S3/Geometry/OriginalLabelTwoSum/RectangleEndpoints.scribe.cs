// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RectangleEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("RectangleEndpoints"),
        Blocks(
            Node("deletioncut", "deletionCut", "deletionCut",
                "Exact deletion-rectangle endpoint, including every empty-fibre case. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("linkcut", "linkCut", "linkCut",
                "Exact link-rectangle endpoint. L<=D accounts for the fibres already retained in D*delta(Z); an empty projected lower is handled without an ordinary move. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("deletionlift", "deletionLift", "deletionLift",
                "Endpoint-transported deletion rule consumes its proved raw equality. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("linklift", "linkLift", "linkLift",
                "Endpoint-transported link rule consumes its proved raw equality. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
