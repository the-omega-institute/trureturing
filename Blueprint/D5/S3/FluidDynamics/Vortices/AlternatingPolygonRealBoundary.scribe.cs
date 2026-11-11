using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonRealBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealBoundary.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive or negative real eigenvalue is a signed canonical real root. Every complex eigenvalue with nonzero real part is real. The dipole and square have only spectral values on the imaginary axis; this statement does not assert bounded flow.",
        H("Alternating Polygon Real Boundary"), Blocks(
            Paragraph(Text("The source extension is the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior equilibrium, instability and small-spectrum credit. The original Conjecture 4.4 real-root proof and its field, rotation, Fourier and determinant suppliers are reused; no priority certification is made.")),
            Node("positive_eigenvalue_iff", "positive eigenvalue iff", "Every positive real eigenvalue is one of the canonical positive roots, with no extra sign branch.", DescribeRole.Theorem),
            Node("negative_eigenvalue_iff", "negative eigenvalue iff", "Every negative real eigenvalue is the negative of one canonical positive root, and every such root occurs.", DescribeRole.Theorem),
            Node("off_axis_is_real", "off axis is real", "Each complex eigenvalue outside the imaginary axis is real.", DescribeRole.Theorem),
            Node("small_spectral_neutrality", "small spectral neutrality", "Dipole and square have no complex eigenvalue with nonzero real part.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-real-boundary-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
