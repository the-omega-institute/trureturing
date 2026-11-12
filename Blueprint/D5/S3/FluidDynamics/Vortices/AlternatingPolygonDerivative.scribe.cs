using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differentiability is proved on the collision-free domain. Each reported partial derivative is a coordinate of the Frechet derivative applied to the corresponding coordinate direction. Finite linear reconstruction identifies the full derivative with matrix multiplication. This bridge connects the canonical normalized matrix and all physical parameter matrices to the actual field.",
        H("Alternating Polygon Derivative"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("jacobian_entry", "jacobian entry", "Every reported matrix entry is a coordinate of the genuine derivative.", DescribeRole.Theorem),
            Node("fderiv_eq_mulVec", "fderiv eq mulVec", "The full derivative acts by the actual Cartesian Jacobian on every direction.", DescribeRole.Theorem),
            Node("hasFDerivAt_field", "hasFDerivAt field", "A kernel-checked Frechet derivative, with no spectral or matrix assumption.", DescribeRole.Theorem),
            Node("hasFDerivAt_normalized", "hasFDerivAt normalized", "The canonical normalized matrix is the matrix of this same genuine derivative.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-derivative-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
