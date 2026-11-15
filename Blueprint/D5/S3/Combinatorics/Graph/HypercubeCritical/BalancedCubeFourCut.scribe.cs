using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class BalancedCubeFourCutDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFourCut.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-edge cuts of connected balanced induced cubic Q9 graphs have a side of at most two vertices.",
        H("Four-edge cuts have a small side"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4. This theorem further constrains the connected balanced "
                    + "cubic components arising from 258-vertex candidates. It supplies no complete "
                    + "candidate or complete exclusion, and makes no literature-novelty claim.")),
            Describe.Lean(
                DescribeId.Create("balanced-cube-four-cut-small-side"),
                DeclarationHandle.Create(Prefix + "small_side_of_cut_card_eq_four"),
                H("An actual four-edge cut has a small side"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For C,T : Finset Q9, assume the actual induced graph on C is connected "
                            + "and regular of degree three, C satisfies the original IsBalanced "
                            + "predicate, T is a subset of C, and the actual cutEdges C T has "
                            + "cardinality four. Then T or its complement in C has at most two "
                            + "vertices. No cut with at least three vertices on both sides is possible.")),
                    Paragraph(Text(
                        "Suppose both sides have at least three vertices. The three-cut "
                            + "classification and actual local cut degrees force the four cut "
                            + "edges to be a matching. The partial integral switching vector f "
                            + "has energy four. For L = 3I − A, integral energy variation bounds "
                            + "Lf pointwise by two. A coordinate of magnitude two forces a "
                            + "two-point residual shape; using the total switching eigenvector "
                            + "would then violate divisibility by six of integer eigenvector norms. "
                            + "Thus Lf is unit-valued, has support twenty-four, and satisfies "
                            + "A(Lf) = −3Lf. HuangUnitSupportGap excludes precisely this possibility."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeThreeCut")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap"))
        ]));
}
