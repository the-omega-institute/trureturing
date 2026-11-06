// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class GraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Graph.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Graph"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Graph"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Graph"),
        Blocks(
            Node("wheelgraphdata", "wheelGraphData", "wheelGraphData",
                "Actual hub-star/rim-interface wheel. The marked e is rim edge 1--2, not a spoke or a coordinate of this right tree. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("fundamental-rows", "fundamental_rows", "fundamental_rows",
                "These are path-derived rows, not an input equation. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("wheeloriginalroot", "wheelOriginalRoot", "wheelOriginalRoot",
                "Deleting the ACTUAL interface chord row gives E; the full root is A1. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("wheelgraphcertificate", "wheelGraphCertificate", "wheelGraphCertificate",
                "The native supplier certificates consume this actual graph-derived root. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("seedgraphdata", "seedGraphData", "seedGraphData",
                "The native supplier certificates consume this actual graph-derived root. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("seedoriginalroot", "seedOriginalRoot", "seedOriginalRoot",
                "K4's actual star-tree paths compute the seed row root. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("seedgraphcertificate", "seedGraphCertificate", "seedGraphCertificate",
                "K4's actual star-tree paths compute the seed row root. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
