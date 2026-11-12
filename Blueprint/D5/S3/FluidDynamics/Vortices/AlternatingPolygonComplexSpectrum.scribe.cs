using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonComplexSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit roots are zero at r=m, plus or minus i*m/sqrt(2) at r=0, plus or minus i*(m-1)/2 at r=1 when this is an internal label, and plus or minus (m-r)*sqrt(r*r-2)/2 at the remaining labels. The neutral guard takes precedence in the dipole. Classification is exhaustive over all complex numbers, with exact algebraic and geometric multiplicities and no collisions between different folded labels.",
        H("Alternating Polygon Complex Spectrum"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("spectralRoot", "spectralRoot", "One square root of each folded spectral value. The neutral label is handled first, so the dipole does not identify its neutral mode with a nonzero internal mode.", DescribeRole.Definition),
            Node("spectralRoot_sq", "spectralRoot sq", "Each explicit complex root squares to the corresponding folded squared value.", DescribeRole.Theorem),
            Node("all_complex_roots", "all complex roots", "Every complex characteristic root is one of these explicit signed values, and conversely.", DescribeRole.Theorem),
            Node("spectralRoot_ne_zero", "spectralRoot ne zero", "Every label strictly below the neutral label gives a nonzero complex root.", DescribeRole.Theorem),
            Paragraph(Text("For m ≥ 1 and folded labels r,s ≤ m, a common signed root μ has μ² equal to both squaredValue m r and squaredValue m s by spectralRoot_sq; the sign disappears on squaring. Injectivity of the real-to-complex embedding gives equality of these real squared values, and AlternatingPolygonMultiplicity.squaredValue_injective gives r = s. Thus different folded labels cannot share a signed root, including the imaginary families and the neutral label. This is a consequence of the existing square and injectivity arguments.")),
            Node("signed_root_multiplicities", "signed root multiplicities", "Complete nonzero algebraic and geometric multiplicities of both signed roots.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-complex-spectrum-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
