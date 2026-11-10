using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class GraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Graph.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Graph",
            "Original labelled roots are computed from unique paths in actual star spanning trees for the wheel and K4 seed.",
            "original-label-two-sum-graph",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Combinatorics.SimpleGraph.Star"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic")),
        H("Graph"),
        Blocks(
            Node("wheelgraphdata", "wheelGraphData", "wheelGraphData",
                "Actual hub-star/rim-interface wheel. The marked e is rim edge 1--2, not a spoke or a coordinate of this right tree. ", DescribeRole.Definition),
            Node("fundamental-rows", "fundamental_rows", "fundamental_rows",
                "These are path-derived rows, not an input equation. ", DescribeRole.Theorem),
            Node("wheeloriginalroot", "wheelOriginalRoot", "wheelOriginalRoot",
                "Deleting the ACTUAL interface chord row gives E; the full root is A1. ", DescribeRole.Theorem),
            Node("wheelgraphcertificate", "wheelGraphCertificate", "wheelGraphCertificate",
                "The native supplier certificates consume this actual graph-derived root. ", DescribeRole.Definition),
            Node("seedgraphdata", "seedGraphData", "seedGraphData",
                "The native supplier certificates consume this actual graph-derived root. ", DescribeRole.Definition),
            Node("seedoriginalroot", "seedOriginalRoot", "seedOriginalRoot",
                "K4's actual star-tree paths compute the seed row root. ", DescribeRole.Theorem),
            Node("seedgraphcertificate", "seedGraphCertificate", "seedGraphCertificate",
                "K4's actual star-tree paths compute the seed row root. ", DescribeRole.Definition)
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
