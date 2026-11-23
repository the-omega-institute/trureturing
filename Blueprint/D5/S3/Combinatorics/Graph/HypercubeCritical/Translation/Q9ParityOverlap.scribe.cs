using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation;

internal sealed class Q9ParityOverlapDocument : IScribeDocumentDefinition
{
    private const string Critical = "D5/S3/Combinatorics/Graph/HypercubeCritical";
    private const string Module = Critical + "/Translation/Q9ParityOverlap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced cubic nine-cube supports have no one-vertex parity intersection under XOR translation.",
        H("Parity intersections of translated cubic supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-parity-overlap"),
                DeclarationHandle.Create(Module + ".parity_overlap_card_ne_one"),
                H("A translated intersection on either parity has cardinality different from one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C and D be supports in the Boolean nine-cube. Assume each induced "
                        + "graph is 3-regular and switching-balanced for Huang's fixed edge "
                        + "signs. For every XOR translation a and each parity b, the number of "
                        + "vertices of parity b in the intersection of C with a + D differs "
                        + "from one. The zero translation gives the same test for C and D.")),
                    Paragraph(Text(
                        "XOR preserves induced adjacency and degree. Huang edge covariance "
                        + "supplies a diagonal sign that transports the switching function. "
                        + "The ambient eigenvector theorem gives an eigenvalue-3 switching "
                        + "vector with entries 0 and ±1. Reducing those entries modulo 3 and "
                        + "retaining a single parity gives a Huang kernel word with exactly "
                        + "the selected support on that parity.")),
                    Paragraph(Text(
                        "The symmetric unit-weight Huang matrix over the ternary field has "
                        + "image equal to kernel because the sum of the nine squared weights "
                        + "vanishes and a coordinate weight is nonzero. Any two kernel words "
                        + "therefore pair to zero. A singleton intersection contributes one "
                        + "nonzero product to that pairing, a contradiction.")),
                    Paragraph(Text(
                        "In the nine-cube component geometry of Hong–Wu–Xia Problem 2, this "
                        + "excludes any relative placement of balanced cubic components that "
                        + "creates exactly one shared vertex on a parity. The test also "
                        + "applies to self-translates and disconnected balanced cubic supports. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Critical + "/BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(Critical + "/BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create(Critical + "/ComponentBoundary/Q9IsotropicHuang")),
            DocumentEdge.Dependency.Create(GidRef.Create(Critical + "/ComponentBoundary/Q9SignedContactCells")),
            DocumentEdge.Dependency.Create(GidRef.Create(Critical + "/ComponentBoundary/Q9WeightedBoundaryGram")),
            DocumentEdge.Dependency.Create(GidRef.Create(Critical + "/Translation/HuangTranslationObstruction")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeSubQuorum"))
        ]));
}
