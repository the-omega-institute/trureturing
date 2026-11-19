using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport;

internal sealed class Q9SixtySixDiameterProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixDiameterProbe", H("Q9SixtySixDiameterProbe"),
        Blocks(
            Paragraph(Text("Exclude Hamming distances eight and nine among the vertices of a 66-vertex Huang-balanced induced cubic support in the nine-cube. A distance-eight pair gives two disjoint radius-three balls of size thirty. The six residual vertices cannot supply enough crossing edges in the common coordinate. A neighbor of one endpoint reduces distance nine to distance eight. This restricts the 66-vertex branch of Hong–Wu–Xia Section 7 Problem 2.")),
            Describe.Lean(
                DescribeId.Create("q9-sixty-six-diameter-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe.claim"),
                H("claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A 66-vertex Huang-balanced induced cubic support in the nine-cube contains two vertices at Hamming distance greater than seven."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-sixty-six-diameter-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe.result"),
                H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every pair in a 66-vertex Huang-balanced induced cubic support in the nine-cube has Hamming distance at most seven."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixResidualCountingProbe"))
        ]));
}
