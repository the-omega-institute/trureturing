using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonPhysicalSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalSpectrum.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive b and Omega, all algebraic and geometric multiplicities transport at the scaled complex value. Every nonzero eigenvalue is semisimple. Every actual invariant block transports, and the real stable and unstable spaces retain dimension 2*(m-2).",
        H("Alternating Polygon Physical Spectrum"), Blocks(
            Paragraph(Text("The source extension is the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior equilibrium, instability and small-spectrum credit. The original Conjecture 4.4 real-root proof and its field, rotation, Fourier and determinant suppliers are reused; no priority certification is made.")),
            Node("physical_algebraic_multiplicity", "physical algebraic multiplicity", "Algebraic multiplicities are preserved at every scaled complex value, including zero.", DescribeRole.Theorem),
            Node("physical_geometric_multiplicity", "physical geometric multiplicity", "Every complex eigenspace has the same dimension at its scaled physical eigenvalue.", DescribeRole.Theorem),
            Node("physical_nonzero_semisimple", "physical nonzero semisimple", "Every nonzero eigenvalue of the actual physical derivative is semisimple.", DescribeRole.Theorem),
            Node("physical_block_restriction", "physical block restriction", "Every actual invariant block is preserved by positive parameter scaling.", DescribeRole.Theorem),
            Node("physicalRealOperator", "physicalRealOperator", "The actual real Cartesian derivative is evaluated at the radius selected by b and Omega.", DescribeRole.Definition),
            Node("physicalRealOperator_eq", "physicalRealOperator eq", "The real physical derivative equals the positive scalar 2*Omega times the canonical real operator.", DescribeRole.Theorem),
            Node("physical_real_eigenspace", "physical real eigenspace", "Scaling the actual derivative and eigenvalue by the same nonzero scalar preserves the real eigenspace.", DescribeRole.Theorem),
            Node("physicalStableSpace", "physicalStableSpace", "The negative physical spectral sum uses the scaled negative roots.", DescribeRole.Definition),
            Node("physicalUnstableSpace", "physicalUnstableSpace", "The positive physical spectral sum uses the scaled positive roots.", DescribeRole.Definition),
            Node("physical_real_spaces", "physical real spaces", "Positive parameter scaling leaves both actual real signed spectral spaces equal to their normalized counterparts.", DescribeRole.Theorem),
            Node("physical_positive_eigenvalue_iff", "physical positive eigenvalue iff", "Every positive real eigenvalue of the actual physical derivative is exactly a scaled canonical positive root.", DescribeRole.Theorem),
            Node("physical_negative_eigenvalue_iff", "physical negative eigenvalue iff", "Every negative real eigenvalue of the actual physical derivative is exactly a scaled canonical negative root.", DescribeRole.Theorem),
            Node("physical_stable_exhaustive", "physical stable exhaustive", "The finite negative spectral sum equals the supremum over all negative real eigenspaces.", DescribeRole.Theorem),
            Node("physical_unstable_exhaustive", "physical unstable exhaustive", "The finite positive spectral sum equals the supremum over all positive real eigenspaces.", DescribeRole.Theorem),
            Node("physical_real_dimensions", "physical real dimensions", "For m at least three, both full physical real spectral spaces have dimension 2*(m-2).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-physical-spectrum-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
