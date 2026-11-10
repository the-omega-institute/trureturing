using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonCartesianChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Use the exact source radial/tangential vectors v0=(0,1) and v1=(s/(1-m*m/2),0), and rotate them into actual real Cartesian displacements. Canonical inverse-chord sums prove the chain equations. The endpoint is nonzero, and the resulting real linear drift orbit is unbounded, also for the dipole and square.",
        H("Alternating Polygon Cartesian Chain"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("radial0", "radial0", "The real source eigenvector has zero radial and constant unit tangential component.", DescribeRole.Definition),
            Node("radial1", "radial1", "The real source generalized vector has alternating radial component s/(1-m squared / 2) and zero tangential component.", DescribeRole.Definition),
            Node("cartesian0", "cartesian0", "Apply the existing radial/tangential rotation to the source eigenvector.", DescribeRole.Definition),
            Node("cartesian1", "cartesian1", "Apply the same actual Cartesian rotation to the source generalized vector.", DescribeRole.Definition),
            Node("cartesian_chain", "cartesian chain", "The exact real Cartesian chain corresponding to v0=(0,1), v1=(s/d,0).", DescribeRole.Theorem),
            Node("cartesian0_ne_zero", "cartesian0 ne zero", "The rotated real tangential source vector is nonzero.", DescribeRole.Theorem),
            Node("unbounded_linear_drift", "unbounded linear drift", "The complete real linearized flow has an unbounded orbit, even in the dipole and square.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-cartesian-chain-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
