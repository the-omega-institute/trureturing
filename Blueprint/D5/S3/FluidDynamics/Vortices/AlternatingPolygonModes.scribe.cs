using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonModesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Folded modes retain one endpoint copy and two internal copies. The complete characteristic polynomial includes zero and every complex root after coefficient extension. The separate dipole and square polynomials use the actual Cartesian derivative. The paired restriction argument proves nonzero generalized eigenspaces equal ordinary eigenspaces.",
        H("Alternating Polygon Modes"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("fold", "fold", "Folded modes retain one endpoint copy and two internal copies. The complete characteristic polynomial includes zero and every complex root after coefficient extension. The separate dipole and square polynomials use the actual Cartesian derivative. The paired restriction argument proves nonzero generalized eigenspaces equal ordinary eigenspaces.", DescribeRole.Definition),
            Node("ell", "ell", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Definition),
            Node("fold_le", "fold le", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("ell_fold", "ell fold", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("ell_shift", "ell shift", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("mode_product", "mode product", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("ell_add_one_ne_zero", "ell add one ne zero", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("gamma_zero_iff", "gamma zero iff", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("fold_eq_iff", "fold eq iff", "Folding retains exactly the pair of opposite cyclic labels.", DescribeRole.Theorem),
            Node("fold_fibre_card", "fold fibre card", "End labels occur once; every interior folded label occurs twice.", DescribeRole.Theorem),
            Node("charpoly_folded", "charpoly folded", "Folded mode factors, with endpoint multiplicity one and interior multiplicity two. This identity includes the separate small polygons.", DescribeRole.Theorem),
            Node("charpoly_factored", "charpoly factored", "The complete normalized polynomial at every m >= 3.", DescribeRole.Theorem),
            Node("dipole_charpoly", "dipole charpoly", "Dipole polynomial, derived separately from the all-mode identity.", DescribeRole.Theorem),
            Node("square_charpoly", "square charpoly", "The square constants follow from the actual Cartesian derivative. They are not the constants printed in BK arXiv v2 Eq. (12).", DescribeRole.Theorem),
            Node("neutral_denominator_ne_zero", "neutral denominator ne zero", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("pairedOperator", "pairedOperator", "The direct sum of the two-dimensional Fourier restrictions.", DescribeRole.Definition),
            Node("paired_nonzero_semisimple", "paired nonzero semisimple", "No two-dimensional off-diagonal restriction has a nontrivial nonzero Jordan chain. This controls generalized eigenspaces, not just polynomial roots.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-modes-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
