using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped7Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped7.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped7"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped7 to the stochastic ellipsoid construction.")),
            Node("claim-1", "log_le_four_sqrt_sqrt", "log le four sqrt sqrt",
                "For every positive natural dimension, log(n) is bounded by four times the fourth root of n.", DescribeRole.Theorem),
            Node("claim-2", "sqrt_ge_1440", "sqrt ge 1440",
                "Above the dimension threshold, the square root of the dimension is at least 1440.", DescribeRole.Theorem),
            Node("claim-3", "sqrt_sqrt_ge", "sqrt sqrt ge",
                "Above the dimension threshold, the fourth root of the dimension is at least 37.", DescribeRole.Theorem),
            Node("claim-4", "log_div_le", "log div le",
                "Above the dimension threshold, log(n)/n is at most the square of 1/96.", DescribeRole.Theorem),
            Node("claim-5", "r0Adopted_nonneg", "r0Adopted nonneg",
                "The adopted spectral increment allowance is nonnegative.", DescribeRole.Theorem),
            Node("claim-6", "etaAdopted_nonneg", "eta Adopted nonneg",
                "The adopted matrix-walk step parameter is nonnegative.", DescribeRole.Theorem),
            Node("claim-7", "r0Adopted_le", "r0Adopted le",
                "Above the dimension threshold, the adopted spectral increment allowance is at most one quarter.", DescribeRole.Theorem),
            Node("claim-8", "c3_mul_eta_le", "c3 mul eta le",
                "Above the dimension threshold, the product of the contact threshold and the matrix-walk step parameter is at most one quarter.", DescribeRole.Theorem),
            Node("claim-9", "one_le_a0C", "one le a0C",
                "For dimensions at least two, the scalar initial quadratic form has coefficient at least one.", DescribeRole.Theorem),
            Node("claim-10", "sqrt_hd_le", "sqrt hd le",
                "Above the dimension threshold, the square root of the step size times the symmetric-matrix coordinate count is bounded by 1/(n^3 sqrt(n)).", DescribeRole.Theorem),
            Node("claim-12", "B_adopted_nonneg", "B adopted nonneg",
                "Above the dimension threshold, the adopted accumulated-error coefficient is nonnegative.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
