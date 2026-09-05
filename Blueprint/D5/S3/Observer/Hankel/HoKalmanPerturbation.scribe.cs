using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class HoKalmanPerturbationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite noisy Ho-Kalman reconstruction with explicit arithmetic certificates.",
        H("HoKalmanPerturbation"),
        Blocks(
            Describe.Lean(DescribeId.Create("norm-le-of-row-sum-le"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_row_sum_le"), H("norm le of row sum le"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Mathlib's induced infinity operator norm is bounded by a common row-sum budget, including empty matrix shapes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("norm-le-of-entrywise-le"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPerturbation.norm_le_of_entrywise_le"), H("norm le of entrywise le"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A uniform entrywise error becomes an operator-norm error multiplied by the number of columns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("true-det-ne-zero-of-inverse-margin"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPerturbation.true_det_ne_zero_of_inverse_margin"), H("true det ne zero of inverse margin"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The inverse of the observed block and a strict perturbation margin force the unknown true block to be nonsingular. The proof uses the existing complete-normed-ring Neumann-series theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-error-identity"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_identity"), H("solve error identity"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Distributivity and the two actual matrix equations derive the solve error identity. No perturbation identity is accepted as an independent assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-error-le"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPerturbation.solve_error_le"), H("solve error le"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A scalar inequality absorbs the unknown true-solution norm and yields a posterior error bound in observed quantities and certified noise budgets."))), DescribeRole.Theorem)),
        []));
}
