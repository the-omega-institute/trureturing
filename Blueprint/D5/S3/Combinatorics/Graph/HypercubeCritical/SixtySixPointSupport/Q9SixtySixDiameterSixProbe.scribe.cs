using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport;

internal sealed class Q9SixtySixDiameterSixProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixDiameterSixProbe", H("Q9SixtySixDiameterSixProbe"),
        Blocks(
            Paragraph(Text("If the diameter is at most six, the distance inequalities force one coordinate split into halves of size 33 and eight splits with a smaller half of size 21. Projecting away the balanced coordinate leaves thirty vertices of weight two. There are only twenty-eight weight-two projections and at most one may occur twice. This excludes diameter six in the 66-vertex branch of Hong–Wu–Xia Section 7 Problem 2.")),
            Describe.Lean(
                DescribeId.Create("q9-sixty-six-distance-seven-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterSixProbe.huang_balanced_cubic_sixty_six_exists_distance_seven"),
                H("Distance seven"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every 66-vertex Huang-balanced induced cubic support of the nine-cube has a pair at Hamming distance seven."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDistanceSumProbe"))
        ]));
}
