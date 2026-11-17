using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonJordanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonJordan.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compose the existing Cartesian radial/tangential rotation with the actual DFT equivalence. This conjugates the actual complexified Cartesian derivative to all paired restrictions. Generalized eigenspaces are transported through that same equivalence. Every nonzero eigenvalue is semisimple for every m at least one.",
        H("Alternating Polygon Jordan"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("actualOperator", "actualOperator", "The actual complexification, acting on Cartesian displacements.", DescribeRole.Definition),
            Node("modeOperator", "modeOperator", "The full paired Fourier operator acts by the two off-diagonal coefficients at each cyclic label.", DescribeRole.Definition),
            Node("rotationCoordinates", "rotationCoordinates", "The existing orthogonal rotation, used as an actual coordinate equivalence.", DescribeRole.Definition),
            Node("cartesianCoordinates", "cartesianCoordinates", "Cartesian -> radial/tangential -> paired Fourier coordinates.", DescribeRole.Definition),
            Node("actual_normal_form", "actual normal form", "Every coordinate, and therefore every invariant block, belongs to the actual Cartesian derivative, with no assumed spectral hypothesis.", DescribeRole.Theorem),
            Node("actual_nonzero_semisimple", "actual nonzero semisimple", "Full generalized eigenspaces transport through the actual Fourier similarity; the nonzero restriction argument applies to all complex \\u03bc.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-jordan-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
