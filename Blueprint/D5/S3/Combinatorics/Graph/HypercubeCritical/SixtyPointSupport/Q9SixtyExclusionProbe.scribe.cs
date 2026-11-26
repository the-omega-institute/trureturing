using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9SixtyExclusionProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtyExclusionProbe", H("Q9SixtyExclusionProbe"),
        Blocks(
            Paragraph(Text("Exclude cardinality sixty for a Huang-balanced induced cubic support in the nine-cube. Coordinate halves have at least twenty-two vertices and the support has diameter at most seven. The signed distance-seven partner graph bounds the total ordered distance sum by 15000, while the coordinate halves give a lower bound of 15048. This excludes one component size in Hong–Wu–Xia Section 7 Problem 2.")),
            Describe.Lean(
                DescribeId.Create("q9-sixty-support-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe.claim"),
                H("claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists a Huang-balanced induced cubic subgraph of the nine-cube on sixty vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-sixty-support-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe.result"),
                H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is no induced cubic Huang-balanced subgraph of the nine-cube with sixty vertices."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SignedPartnerCapacityProbe")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyDiameterUpperProbe"))
        ]));
}
