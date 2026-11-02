using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class CosphericalUnitLocusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/CosphericalUnitLocus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact common unit-distance locus of a nonempty cospherical anchor family.",
        H("Cospherical anchors and their common unit locus"),
        Blocks(
            Paragraph(Text(
                "This is the classical orthogonal decomposition of a sphere intersection. "
                + "Orthogonal projection and subspace operations are reused from Mathlib. "
                + "The anchor family is indexed by an arbitrary type with a chosen index; "
                + "it need not be injective or finite. The ambient real inner product "
                + "space is finite-dimensional.")),
            Node("anchor-direction", "anchorDirection", "Anchor affine direction",
                "The direction is the linear span of all differences x(i)-x(i0) from "
                + "the chosen base anchor.", DescribeRole.Definition),
            Node("anchor-center", "anchorCenter", "Constructed affine center",
                "Subtract from the base anchor its orthogonal projection onto the "
                + "anchor direction. The result c is perpendicular to that direction "
                + "and every anchor minus c lies in it.", DescribeRole.Definition),
            Node("common-unit-locus", "common_unit_locus_iff", "Exact unit-locus equivalence",
                "For every real r, every anchor family x all of whose points have norm r, "
                + "every chosen base index i0 and every ambient point p, all distances "
                + "from p to the anchors equal one if and only if p-c belongs to the "
                + "orthogonal complement of the anchor direction and norm(p-c) squared "
                + "equals one minus r squared plus norm(c) squared. Both directions "
                + "are proved for the same point p. Subtracting the squared distance "
                + "equations establishes perpendicularity to every anchor difference, "
                + "and orthogonal decomposition supplies the remaining scalar equation. "
                + "The statement includes empty intersections and codimension-one "
                + "two-point intersections. It does not itself assert nonemptiness, "
                + "positive dimension, finite avoidance or a graph embedding.", DescribeRole.Theorem),
            Node("common-unit-avoidance", "exists_common_unit_avoiding",
                "Faithful choices from a common-unit locus",
                "Assume the common anchor norm r is nonnegative and less than one, "
                + "and the orthogonal complement of the anchor direction has dimension "
                + "at least two. Every ambient-open patch containing a common-unit "
                + "point contains one that avoids unit distance to a prescribed finite "
                + "family of forbidden centers and avoids every point in a second "
                + "finite family. Each forbidden center z must have norm different "
                + "from r or lie outside the anchor affine hull, expressed as "
                + "z-c not belonging to the anchor direction. If its restricted "
                + "normal vanished and its unit sphere contained the allowed sphere, "
                + "orthogonal decomposition would force both affine-hull membership "
                + "and norm r, contradicting this hypothesis. The positive radius "
                + "is constructed as the square root of one minus r squared plus "
                + "norm(c) squared. The proved affine-sphere avoidance theorem then "
                + "makes all finite choices simultaneously. No graph-level claim "
                + "or arbitrary partial-placement extension follows without its "
                + "additional geometric and combinatorial hypotheses.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
