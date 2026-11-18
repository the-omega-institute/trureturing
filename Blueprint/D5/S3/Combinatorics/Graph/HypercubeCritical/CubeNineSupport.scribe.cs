using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class CubeNineSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeNineSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty Q9 set of at most nine vertices with no singleton neighbor is a full vertex neighborhood.",
        H("Nine-point supports without singleton neighbors"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4. This classifies small actual cube supports "
                    + "needed for the integral Huang residual argument. It supplies "
                    + "neither a 258-vertex construction nor a complete exclusion, "
                    + "and no literature-priority claim is made.")),
            Describe.Lean(
                DescribeId.Create("cube-nine-support-neighborhood-classification"),
                DeclarationHandle.Create(Prefix + "eq_neighbors_of_no_singleton"),
                H("A full neighborhood is the only small support without a singleton neighbor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a nonempty finset of actual Q9 vertices with "
                            + "S.card ≤ 9. If every vertex y has a number of neighbors "
                            + "in S different from one, then S is exactly "
                            + "Finset.univ.filter (fun x => (hypercube 9).Adj y x) "
                            + "for some y. No parity, common-center, distance-two "
                            + "clique or classification certificate is assumed.")),
                    Paragraph(Text(
                        "The absence of singleton neighbors makes the two-coordinate "
                            + "differences from each selected point cover all nine "
                            + "directions, so each point has at least five selected "
                            + "vertices at distance two. A pair at distance other "
                            + "than two or four has disjoint such neighbor sets, "
                            + "requiring at least twelve points. For a distance-four "
                            + "pair, covering the other five coordinates requires "
                            + "at least three private neighbors on each side; the "
                            + "degree-five bounds then require at least ten points. "
                            + "Thus all selected pairs are at distance two. Their "
                            + "two-element difference sets are pairwise intersecting "
                            + "and cover nine coordinates, forcing a common coordinate "
                            + "and hence the full neighborhood."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport"))
        ]));
}
