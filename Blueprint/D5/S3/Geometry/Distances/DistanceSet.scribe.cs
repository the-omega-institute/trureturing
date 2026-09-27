using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Distances;

internal sealed class DistanceSetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Distances/DistanceSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distance sets of finite point sets, and the three-point bound for equilateral sets in the "
            + "Euclidean plane.",
        H("Distance sets and equilateral point sets"),
        Blocks(
            Paragraph(Text(
                "The distance set of a finite set of points collects the distances between distinct "
                    + "members, identifying repetitions. A finite point set has finitely many pairs "
                    + "in any metric space, so the definitions need no Euclidean or "
                    + "finite-dimensional hypothesis; the empty and one-point sets have no "
                    + "distances.")),
            Describe.Lean(
                DescribeId.Create("distance-set-definition"),
                DeclarationHandle.Create(Prefix + "distanceSet"),
                H("The distance set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "distanceSet P is the set of real numbers realised as the distance between two "
                        + "distinct members of P."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distance-set-count"),
                DeclarationHandle.Create(Prefix + "distinctDistances"),
                H("The number of distinct distances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "distinctDistances P is the cardinality of the distance set, obtained from the "
                        + "image of the finite set of pairs rather than from a convention for "
                        + "infinite sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distance-set-equilateral-bound"),
                DeclarationHandle.Create(Prefix + "card_le_three_of_pairwise_dist_eq"),
                H("Equilateral sets in the plane have at most three points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite set of points in the Euclidean plane whose distinct members are all at "
                        + "one common distance has at most three elements. The bound is attained by "
                        + "an equilateral triangle."))),
                DescribeRole.Theorem)),
        []));
}
