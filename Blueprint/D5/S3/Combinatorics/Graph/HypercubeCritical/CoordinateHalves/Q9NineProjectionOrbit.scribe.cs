using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9NineProjectionOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-coordinate projections of balanced cubic supports",
        H("Four-coordinate projections of 72-vertex balanced cubic supports"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-four-projection-excludes-nine"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjectionOrbit."
                    + "four_projection_card_ne_nine"),
            H("Exclusion of nine realized patterns"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a Huang-balanced induced cubic support in the nine-cube have 72 vertices, "
                    + "with at least 30 in each coordinate half. Its projection to any four "
                    + "distinct axes cannot realize exactly nine patterns.")),
                Paragraph(Text(
                    "A missing triple pattern gives a complement edge of the four-coordinate "
                    + "projection. Distinct parallel complement edges must be antipodal. "
                    + "The signed adjacency on the four selected coordinates squares to four times "
                    + "the identity. It forces a neighbor at every realized pattern and four neighbors "
                    + "at the neighbor of any projected leaf. The orbit classification reduces "
                    + "nine-point patterns satisfying these constraints to one representative "
                    + "under bit translations and coordinate permutations.")),
                Paragraph(Text(
                    "The cube action transports regularity and Huang balance to the representative. "
                    + "On each complementary five-coordinate fiber, the switching vector and its "
                    + "four-coordinate signed image vanish at missing patterns. Four exterior rows "
                    + "force the switching vector to vanish at code 1 in every fiber, contradicting "
                    + "its realization. This excludes a projection size in the order-72 branch "
                    + "of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-four-projection-at-least-ten"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjectionOrbit."
                        + "four_projection_card_ge_ten"),
                H("At least ten realized patterns on four axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same half-size hypothesis, each four-coordinate projection "
                        + "realizes at least ten patterns. The matching bound gives at least eight "
                        + "and the nine-pattern exclusion removes one of the two smallest sizes.")),
                    Paragraph(Text(
                        "An eight-pattern orbit has an induced eight-cycle as its representative. "
                        + "The signed adjacency forces occupation to be constant along two-step "
                        + "walks in each fiber, giving two parity classes of four vertices. Counts "
                        + "in the projected directions give six full and six exclusive fibers.")),
                    Paragraph(Text(
                        "The two parity classes define two induced subgraphs of the remaining "
                        + "five-cube. Their overlap, degree counts, and signed row conditions "
                        + "force a coordinate half of weight five, with one unit per exclusive "
                        + "fiber and two per full fiber. Each unit accounts for four vertices. "
                        + "The resulting 20-vertex half contradicts the lower bound 30, which "
                        + "is preserved by the cube action."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection"))
        ]));
}
