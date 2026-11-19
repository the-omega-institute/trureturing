using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointPentagonSignsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common centers and odd Huang signs", H("Common centers and odd Huang signs"),
        Blocks(
            Paragraph(Text("Five distinct same-parity cube vertices at pairwise Hamming distance two have a common cube neighbor. Relative to one vertex, the other four differences are distinct two-element sets with pairwise one-element intersections. Four such sets share an element: if two meet at a and a third omits a, the three sets form a triangle, which admits no fourth distinct pair meeting all three.")),
            Paragraph(Text("Let five actual selected vertices be neighbors of a common cube center, joined cyclically by actual degree-two middles. The center cannot be one of these middles, because it has at least three distinct selected neighbors. Each middle is consequently the other corner of its genuine coordinate square. Anticommutation of the original Huang direction operators and the original switching function force five successive sign reversals, a contradiction. The center need not belong to the support."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagon")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))
        ]));
}
