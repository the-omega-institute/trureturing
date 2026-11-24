using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation;

internal sealed class OrderThreeFixedAxisEdgesDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Owner = Cube + "Translation/OrderThreeFixedAxisEdges.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-three orbits of fixed-axis edges in a balanced cubic support",
        H("Fixed directions and translation periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-axis-edges-in-triples"),
                DeclarationHandle.Create(Owner + "three_dvd_directionEdges"),
                H("A fixed axis has a multiple of three selected edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a cube symmetry stabilize a balanced induced cubic support. Assume the symmetry and its axis permutation have order dividing three and the axis permutation fixes at most three axes. At a fixed vertex incident to a fixed-axis edge, the three selected directions form an invariant set with at least one fixed element. A nontrivial orbit would require three other directions, so the three directions exhaust the fixed axes.")),
                    Paragraph(Text("The other endpoint is fixed and has the same three directions. A second direction then produces a selected coordinate square, forbidden by Huang balance. The symmetry therefore has no fixed selected edge in the chosen axis. An action of order dividing three cannot exchange two endpoints of a fixed edge, so all edge orbits have size three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-axis-translation-divisibility"),
                DeclarationHandle.Create(Owner + "thirtySix_dvd_card_of_fixed_axis_and_period"),
                H("A fixed axis and an off-axis translation period force divisibility by thirty-six"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the preceding order-three hypotheses, suppose the support lies in Q9 and admits an XOR translation period that changes a coordinate other than the chosen fixed axis. The translation pairs all selected edges in that axis. The edge count is divisible by both two and three. In Q9 the balance identity equates six times the directional edge count with the total size of the support, giving divisibility by thirty-six.")),
                    Paragraph(Text("If the coordinate permutation (012)(345) stabilizes the support, axes 6, 7 and 8 are fixed. Every nonzero translation period moves a coordinate outside at least one of those axes. Thus only 72, 108 and 144 pass this divisibility test in the interval 66–144 for the periodic double-three-cycle branch of Hong, Wu and Xia’s Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "Translation/HuangTranslationObstruction"))
        ]));
}
