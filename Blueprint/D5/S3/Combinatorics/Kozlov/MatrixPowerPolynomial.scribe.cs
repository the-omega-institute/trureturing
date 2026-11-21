using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class MatrixPowerPolynomialDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Writing a unitriangular matrix as the identity plus a strictly upper triangular matrix gives a finite binomial expansion of its powers.",
        H("Polynomial entries of upper unitriangular matrix powers"),
        Blocks(
            Node("offdiag", "offDiag", "The part off the diagonal", DescribeRole.Definition,
                "Keep the original entries away from the diagonal and put zero on the diagonal."),
            Node("one-add-offdiag", "one_add_offDiag", "Split off the identity matrix", DescribeRole.Theorem,
                "The diagonal-one hypothesis supplies equality on the diagonal and the other entries are unchanged."),
            Node("pow-apply-eq-zero", "pow_apply_eq_zero", "Powers impose increasing state distance", DescribeRole.Theorem,
                "Every nonzero term in matrix multiplication traverses a strictly increasing chain of indices. Induct on the exponent."),
            Node("pow-eq-zero-of-le", "pow_eq_zero_of_le", "Strict triangularity gives nilpotence", DescribeRole.Theorem,
                "No chain of the required length can fit in the finite index range once the exponent reaches its size."),
            Node("pow-eq-sum-choose", "pow_eq_sum_choose", "The finite binomial expansion of powers", DescribeRole.Theorem,
                "The identity commutes with the off-diagonal part. Apply the binomial theorem and discard the vanishing powers beyond the matrix size."),
            Node("powerpolynomial", "powerPolynomial", "The rational polynomial of one power entry", DescribeRole.Definition,
                "Sum the entries of the off-diagonal powers against the falling-binomial polynomials, through the last possibly nonzero power."),
            Node("powerpolynomial-eval", "powerPolynomial_eval", "Natural evaluations recover matrix power entries", DescribeRole.Theorem,
                "At a natural input each falling-binomial polynomial evaluates to the corresponding binomial coefficient. The finite matrix expansion then yields the desired entry."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-matrix-power-polynomial-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
