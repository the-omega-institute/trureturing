using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class LiteralSecondStarCoordinateBoundDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp coordinate bound for a literal standard second star",
        H("A literal second-subdivision star inherits the 25/48 bound"),
        Blocks(
            Paragraph(Text(
                "The standard vertices are the four coordinate unit vectors in the real "
                    + "function space on Fin(4). The literal second closed star is defined "
                    + "from the actual chains of faces and their barycenters. The main theorem "
                    + "transports a point of that literal star to a parent flag, expands its "
                    + "parent convex combination into barycentric face weights, and applies "
                    + "the sharp parent-star estimate.")),
            Describe.Lean(
                DescribeId.Create("literal-second-star-standard-vertices"),
                DeclarationHandle.Create(Root + "standardVertices"),
                H("The four standard coordinate vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "standardVertices assigns to each element of Fin(4) the corresponding "
                        + "coordinate unit vector in the real function space on Fin(4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("literal-second-star-standard-vertices-independent"),
                DeclarationHandle.Create(Root + "standardVertices_affineIndependent"),
                H("The standard coordinate vertices are affinely independent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four unit vectors have unique affine coefficients: equality of two "
                        + "affine combinations can be read one coordinate at a time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-second-star-coordinate-bound"),
                DeclarationHandle.Create(Root + "literal_standard_closed_star_coordinate_bound"),
                H("Every coordinate of a literal standard closed star is at least 25/48"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If x belongs to the literal second closed star at the standard "
                            + "vertex i, then its i-th coordinate is at least 25/48.")),
                    Paragraph(Text(
                        "The literal-to-parent-star correspondence supplies a permutation whose "
                            + "first flag entry is i. A convex-hull representation of x is "
                            + "expanded into coefficients on the four parent flag vertices. "
                            + "The parent-star characterization makes the zeroth coefficient "
                            + "maximal, and the parent linear estimate then gives the stated "
                            + "lower bound. The first coordinate of the parent flag vertex of "
                            + "rank k is exactly 1/(k+1), so the resulting weighted expression "
                            + "is the i-th coordinate of x."))),
                DescribeRole.Theorem)),
        []));
}
