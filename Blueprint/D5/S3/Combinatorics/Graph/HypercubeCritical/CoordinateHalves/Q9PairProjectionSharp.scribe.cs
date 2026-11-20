using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9PairProjectionSharpDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate projections at half-size 28",
        H("Four stars and the missing two-coordinate pattern"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-pair-projection-at-twenty-eight"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp."
                    + "pair_projection_surjective_of_twenty_eight"),
            H("Every coordinate pair realizes all four patterns"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Consider a 72-vertex Huang-balanced induced cubic support in the nine-cube "
                    + "with each coordinate half of size at least 28. If a two-bit pattern is "
                    + "absent, the two specified halves must both have size 28. The opposite "
                    + "seven-dimensional fiber then consists of four disjoint three-leaf stars.")),
                Paragraph(Text(
                    "The missing pattern identifies the two adjacent signed fibers. Reducing "
                    + "their signed relation modulo two shows that the opposite occupation is fixed "
                    + "by ordinary adjacency over the field of two elements. The parity defects "
                    + "of the four stars cancel. Coordinate translations and the stabilizer of "
                    + "the first star reduce the cancellation to two residual cases, which force "
                    + "the stars to share their three directions.")),
                Paragraph(Text(
                    "In the resulting three-cube by four-cube product, the signed row on each "
                    + "parallel star determines the adjacent fibers. Their cardinality forces a "
                    + "20-vertex half on a star axis. The cube action carries that cut back to the "
                    + "original support, contradicting the lower bound 28."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-four-projection-at-least-ten-at-twenty-eight"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp."
                        + "four_projection_card_ge_ten_of_twenty_eight"),
                H("At least ten patterns on any four distinct axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pair surjectivity allows the antipodal complement-edge argument on any "
                    + "four distinct axes. The eight- and nine-pattern exclusions then give "
                    + "the ten-pattern lower bound for the order-72 branch of Hong, Wu and Xia, "
                    + "arXiv:2610.09483v1, Section 7, Problem 2."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjectionOrbit"))
        ]));
}
