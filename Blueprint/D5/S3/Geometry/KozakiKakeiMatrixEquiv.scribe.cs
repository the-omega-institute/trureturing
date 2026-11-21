using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiMatrixEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiMatrixEquiv.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row operations and column scalings multiply both determinant products by the same nonzero factor.",
        H("Invertible matrix operations and the level equation"),
        Blocks(
            Definition("Square", "Row operations",
                "The square matrix type has two rows and two columns over the rational function field."),
            Definition("scaled", "Left and right multiplication",
                "Apply the square matrix on the left and the diagonal of the column factors on the right."),
            Theorem("scaled_apply", "Entries after scaling",
                "Take the two-term row combination and multiply by the column factor."),
            Theorem("minor_scaled", "Determinant transformation",
                "Each minor acquires the determinant of the left matrix and the two column factors."),
            Theorem("scaled_admissible", "Admissibility after invertible scaling",
                "All the factors in the scaled minor remain nonzero."),
            Theorem("unit_det_ne_zero", "Invertible matrices have nonzero determinant",
                "An invertible square matrix has unit determinant in the coefficient field."),
            Theorem("level_scaled_iff", "Invariance of the written level",
                "Each matching uses every column once. Both products acquire the determinant to the m-th power times the product of all column factors, which can be canceled."),
            Theorem("scaled_comp", "Composition of row and column operations",
                "Left factors multiply in application order and right scalars multiply pointwise."),
            Theorem("matEquivalent_symm", "Symmetry of matrix equivalence",
                "Invert the left matrix and each column factor."),
            Theorem("matEquivalent_trans", "Transitivity of matrix equivalence",
                "Compose the left operations and multiply the diagonal factors pointwise."),
            Theorem("reorder_equiv", "Transport of matrix equivalence",
                "The same left matrix and the correspondingly permuted diagonal factors implement equivalence after column reordering."),
            Theorem("reorder_admissible", "Transport of admissibility",
                "A permutation takes distinct columns to distinct columns."),
            Theorem("level_equiv", "Level invariance under matrix equivalence",
                "The unit witnesses make the common factor nonzero, so matrix-equivalent inputs satisfy the same level equation."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-matrixequiv-" + name.ToLowerInvariant().Replace('_', '-');
}
