using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse coordinate equivalence injects each complete two-dimensional Fourier block into actual Cartesian space. The restriction theorem records its action. Reconstruction and uniqueness certify the complete invariant direct sum. Nonzero geometric multiplicities follow from equality of generalized and ordinary eigenspaces and the characteristic polynomial multiplicities.",
        H("Alternating Polygon Decomposition"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Paragraph(Text("The canonical DFT uses the negative character in the forward transform and the positive character divided by N in its inverse. Thus a unit coordinate of the injected block gives the source vector f^q/N in the radial slot and f^(q+m)/N in the tangential slot. These have exactly the source invariant span U_q; the common nonzero factor 1/N preserves its restriction matrix. The paired tangential index is reduced modulo N=2m.")),
            Node("block", "block", "Injection of the entire two-dimensional Fourier block into actual Cartesian space.", DescribeRole.Definition),
            Node("coordinates_block", "coordinates block", "The complete Cartesian coordinate equivalence sends a block injection to its single Fourier coordinate.", DescribeRole.Theorem),
            Node("block_restriction", "block restriction", "The actual restriction action on each block, including the neutral block.", DescribeRole.Theorem),
            Node("reconstruct", "reconstruct", "Completeness: every Cartesian displacement is the sum of its actual invariant blocks.", DescribeRole.Theorem),
            Node("unique_coefficients", "unique coefficients", "Directness: the complete block expansion has unique coefficients.", DescribeRole.Theorem),
            Node("invariantSpace", "invariantSpace", "The actual invariant subspace belonging to a single Fourier label.", DescribeRole.Definition),
            Node("invariantSpace_finrank", "invariantSpace finrank", "Each actual Cartesian Fourier block has complex dimension two.", DescribeRole.Theorem),
            Node("geometric_eq_algebraic", "geometric eq algebraic", "All complex nonzero geometric multiplicities equal the full algebraic multiplicities.", DescribeRole.Theorem),
            Node("geometric_multiplicity_of_mode", "geometric multiplicity of mode", "Exact geometric multiplicity at each folded label, with all collisions counted.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-decomposition-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
