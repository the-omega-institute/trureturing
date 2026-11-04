using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class LowDegreeFaithfulExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful restoration of vertices with at most two retained neighbors in five-dimensional Euclidean space.",
        H("Restoring low-degree vertices while fixing the old placement"),
        Blocks(
            Paragraph(Text(
                "A faithful placement represents adjacency by distance exactly one in both directions, "
                + "using a single injective map. The retained vertices need not form a whole part of "
                + "a bipartition. It is enough that every omitted vertex has all its neighbors in "
                + "a fixed retained set B and has degree at most two. In the bipartite application, "
                + "all B vertices, including isolates, are retained and only A vertices are restored.")),
            Describe.Lean(
                DescribeId.Create("faithful-extension"),
                DeclarationHandle.Create("D5/S3/Geometry/LowDegreeFaithfulExtension.exists_faithful_extension"),
                H("A faithful extension on the original vertex set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be a finite simple graph on the original vertex type V, let B and s "
                        + "be finite subsets of V with B contained in s, and let p map the subtype s "
                        + "injectively into real Euclidean space with five coordinates. Assume that "
                        + "for every ordered pair u,v in s, adjacency in G is equivalent to "
                        + "distance one between p(u) and p(v). Assume also that distinct vertices "
                        + "of B have p-distance strictly less than two. Every vertex outside s "
                        + "must have its entire neighborhood in B and degree at most two. Then "
                        + "there is one map P on all of V which is injective, satisfies adjacency "
                        + "if and only if distance one for every ordered pair in V, and satisfies "
                        + "P(u)=p(u) for every vertex of s. In particular every old A point and "
                        + "every B point stays fixed. The statement includes diagonal pairs, "
                        + "same-part nonedges, arbitrary isolates and empty vertex sets.")),
                    Paragraph(Text(
                        "For zero neighbors, choose on the sphere of radius two about the origin. "
                        + "No unit sphere can contain that sphere: the constant-distance condition "
                        + "would require four plus a squared norm to equal one. For one neighbor b, "
                        + "use the unit sphere about b. A different center has nonzero restricted "
                        + "normal and hence cuts a proper section. The ambient carrier has real "
                        + "dimension five, and a point of each positive-radius sphere is supplied "
                        + "by the norm-existence theorem.")),
                    Paragraph(Text(
                        "For two distinct neighbors b,c, write m=(b+c)/2 and a=(b-c)/2. "
                        + "Injectivity gives a nonzero a, and the strict diameter bound gives "
                        + "norm(a)<1. The perpendicular complement of the span of a has dimension "
                        + "four. Its sphere of radius sqrt(1-norm(a) squared), translated by m, "
                        + "is nonempty and every point on it has distance one to both b and c. "
                        + "A forbidden center with zero restricted normal lies on the line m+Ra. "
                        + "If its sphere contained the allowed sphere, the squared-radius equation "
                        + "would force its line parameter to be plus or minus one, making it b "
                        + "or c. Old injectivity excludes both alternatives for every nonneighbor. "
                        + "The finite affine-sphere avoidance theorem therefore excludes all "
                        + "unwanted unit distances and all old positions simultaneously.")),
                    Paragraph(Text(
                        "Induction on the number of omitted vertices inserts one such point at "
                        + "a time. Its forbidden centers include every already restored vertex. "
                        + "The new map agrees pointwise with the preceding map, so the retained "
                        + "B diameter bound persists and every same-part nonedge remains nonunit. "
                        + "The finite-sphere avoidance construction is reused directly; no "
                        + "geometric choice principle is assumed as an input. The strict B "
                        + "diameter condition is essential to this construction and is not "
                        + "asserted for arbitrary faithful partial placements."))),
                DescribeRole.Theorem))));
}
