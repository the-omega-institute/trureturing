using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SphereBrouwerObstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euclidean sphere cannot be contracted.",
        H("The Euclidean sphere cannot be contracted"),
        Blocks(Describe.Lean(
            DescribeId.Create("sphere-brouwer-obstruction"),
            DeclarationHandle.Create("D5/S3/Topology/SphereBrouwerObstruction.not_contractible_unit_sphere"),
            H("Noncontractibility from the simplex fixed point theorem"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For every positive natural n, the unit sphere of real Euclidean n-space is not contractible. Ambient dimension one is included.")),
                Paragraph(Text("Suppose a contraction existed. Reverse it and collapse the zero end of the compact cylinder consisting of the unit interval times the sphere. The map sending (t,x) to t times x is a continuous surjection onto the closed unit ball, hence a quotient map. The reversed contraction is constant on each fiber and therefore descends to a continuous retraction of the ball onto its sphere.")),
                Paragraph(Text("Embed the sphere affinely in the standard simplex on n+1 vertices. Its n nonconstant coordinates are (x_i+1)/(2n), and the remaining coordinate is one minus their sum. The affine map with coordinates 2n times the corresponding simplex coordinate minus one is a left inverse. Radially clip its values into the ball, apply the alleged retraction, take the antipode, and return to the simplex. A fixed point supplied by the existing Brouwer theorem would have a unit vector equal to its own antipode, a contradiction.")),
                Paragraph(Text("The simplex fixed point theorem is reused from the attributed Math_XMUM formalization. The retraction argument is a classical consequence and carries no novelty claim."))),
            DescribeRole.Theorem))));
}
