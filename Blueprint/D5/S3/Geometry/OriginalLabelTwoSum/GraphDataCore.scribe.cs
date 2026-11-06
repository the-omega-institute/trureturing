// SOURCE ONLY: actual public declarations below; catalog resolution, emit,
// rendering, registration and native acceptance have not run.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class GraphDataCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Existing GraphData, path, path_eq and rows declarations are moved verbatim from Graph into this unique owner. Graph imports this owner; CutGraphRows consumes it directly. Arbitrary vertices and the original finite Label assumptions are preserved. Source only.",
        H("GraphDataCore"),
        Blocks(
            Describe.Lean(DescribeId.Create("graphdata"), DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/GraphDataCore.GraphData"), H("GraphData"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("D5.S3.Geometry.OriginalLabelTwoSum.GraphData. Existing GraphData, path, path_eq and rows declarations are moved verbatim from Graph into this unique owner. Graph imports this owner; CutGraphRows consumes it directly. Arbitrary vertices and the original finite Label assumptions are preserved. Source only."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path"), DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/GraphDataCore.path"), H("path"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("D5.S3.Geometry.OriginalLabelTwoSum.GraphData.path. Existing GraphData, path, path_eq and rows declarations are moved verbatim from Graph into this unique owner. Graph imports this owner; CutGraphRows consumes it directly. Arbitrary vertices and the original finite Label assumptions are preserved. Source only."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path_eq"), DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/GraphDataCore.path_eq"), H("path_eq"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("D5.S3.Geometry.OriginalLabelTwoSum.GraphData.path_eq. Existing GraphData, path, path_eq and rows declarations are moved verbatim from Graph into this unique owner. Graph imports this owner; CutGraphRows consumes it directly. Arbitrary vertices and the original finite Label assumptions are preserved. Source only."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rows"), DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/GraphDataCore.rows"), H("rows"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("D5.S3.Geometry.OriginalLabelTwoSum.GraphData.rows. Existing GraphData, path, path_eq and rows declarations are moved verbatim from Graph into this unique owner. Graph imports this owner; CutGraphRows consumes it directly. Arbitrary vertices and the original finite Label assumptions are preserved. Source only."))), DescribeRole.Definition)
        )));
}
