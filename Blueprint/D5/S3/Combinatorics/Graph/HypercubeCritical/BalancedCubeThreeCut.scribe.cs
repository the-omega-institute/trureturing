using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class BalancedCubeThreeCutDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeThreeCut.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every three-edge cut in a connected balanced induced cubic Q9 subgraph has a singleton side.",
        H("Three-edge cuts isolate a vertex"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4. This constrains the connected balanced cubic "
                    + "components arising in the study of 258-vertex candidates. "
                    + "It supplies neither a complete candidate nor a complete "
                    + "exclusion; literature novelty remains unverified.")),
            Describe.Lean(
                DescribeId.Create("balanced-cube-three-cut-singleton-side"),
                DeclarationHandle.Create(Prefix + "singleton_side_of_cut_card_eq_three"),
                H("An actual three-edge cut has a singleton side"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For C,T : Finset Q9, assume the actual induced graph on C "
                            + "is connected and regular of degree three, C satisfies "
                            + "the original FALSE-prefix IsBalanced predicate, T ⊆ C, "
                            + "and BalancedCubeCut.cutEdges C T has cardinality three. "
                            + "Then T.card = 1 or (C \\ T).card = 1. Connectedness is "
                            + "an explicit hypothesis. The conclusion permits the "
                            + "three-edge cuts around individual cubic vertices.")),
                    Paragraph(Text(
                        "Let f be the integer partial switching vector, L = 3I − A "
                            + "for the original Huang operator, and Rf = 3 even(f) "
                            + "− A odd(f). The cut energy is three, so the residual "
                            + "has squared norm nine and its Huang image is divisible "
                            + "by three. HuangMinimalResidual supplies its two possible "
                            + "forms. The identities L Rf = 3 Lf and L A = −3 L "
                            + "give Lf = ±Lδ_y directly in both cases.")),
                    Paragraph(Text(
                        "On C the absolute value of Lf at a vertex equals its "
                            + "actual cut degree. A center y outside C would be "
                            + "adjacent to both ends of a cut edge, contradicting "
                            + "the absence of cube triangles. A center in C has "
                            + "cut degree three. Removing it from its side leaves "
                            + "a subset closed under induced adjacency, which "
                            + "connectedness forces to be empty."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeCut")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual"))
        ]));
}
