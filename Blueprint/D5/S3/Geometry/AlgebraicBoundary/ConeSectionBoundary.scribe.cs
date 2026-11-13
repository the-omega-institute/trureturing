using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;
internal sealed class ConeSectionBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The whole compact section and the whole ambient boundary for the original unit.",
        H("Exact original section boundary transport"),
        Blocks(Paragraph(Text("Normalize an actual original interior point with the specified arbitrary positive unit. Salience excludes the vertex from the ambient interior. The normalized point is still in that interior. Its translated kernel chart identifies the whole normalized section with the actual closed convex kernel body, including interior and frontier, by base_chart_geometry. Thus the original section is compact and has nonempty relative interior, and its relative frontier is exactly the ambient cone frontier at unit mass.")),
        Paragraph(Text("For every nonzero original ambient boundary point x, strict positivity gives the positive scalar r=u(x), and x/r is an actual unit-mass boundary point. Conversely every positive multiple of every relative section boundary point is a nonzero ambient boundary point. Both directions retain the entire frontier, with no selected patch or seed. The vertex is excluded exactly in this ray formula and remains in the separate original boundary ideal statement.")))));
}
