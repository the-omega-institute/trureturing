using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonPhysicalDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalDerivative.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Frechet derivative at the positive physical radius is exactly 2*Omega times the normalized Cartesian matrix. The exact source real Cartesian chain transports by rescaling its generalized vector by the inverse of 2*Omega.",
        H("Alternating Polygon Physical Derivative"), Blocks(
            Paragraph(Text("The source extension is the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior equilibrium, instability and small-spectrum credit. The original Conjecture 4.4 real-root proof and its field, rotation, Fourier and determinant suppliers are reused; no priority certification is made.")),
            Node("physical_derivative", "physical derivative", "The physical Frechet derivative is exactly 2*Omega times the canonical Cartesian Jacobian.", DescribeRole.Theorem),
            Node("physical_cartesian_chain", "physical cartesian chain", "The exact source's real Cartesian chain transports to every positive b and Omega.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-physical-derivative-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
