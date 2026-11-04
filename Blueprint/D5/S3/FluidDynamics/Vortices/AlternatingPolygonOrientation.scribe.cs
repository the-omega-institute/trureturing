using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonOrientationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonOrientation.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differentiate the actual Cartesian rotational covariance through an invertible common spatial rotation. This gives the exact derivative intertwining for arbitrary orientation, including the common rotation between the note polygon and the canonical formal polygon.",
        H("Alternating Polygon Orientation"), Blocks(
            Paragraph(Text("The source extension is the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior equilibrium, instability and small-spectrum credit. The original Conjecture 4.4 real-root proof and its field, rotation, Fourier and determinant suppliers are reused; no priority certification is made.")),
            Node("orientation", "orientation", "A common spatial rotation is a genuine invertible Cartesian coordinate map.", DescribeRole.Definition),
            Node("derivative_rotation", "derivative rotation", "Differentiating the Cartesian covariance gives the actual derivative intertwining.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-orientation-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
