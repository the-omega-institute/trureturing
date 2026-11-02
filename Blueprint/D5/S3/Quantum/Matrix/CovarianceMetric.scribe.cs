using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CovarianceMetricDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CovarianceMetric";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular completion of the square and the attained positive-metric Riccati trace minimum used by the Audenaert covariance route.",
        H("Covariance metrics for rectangular matrices"), Blocks(
        Item("rectangular_metric_square", "Rectangular metric completion",
            "For finite index types m and k, a positive definite square metric D and arbitrary rectangular A,C satisfy the exact ordered identity A* D A + C* D inverse C - A* C - C* A = (A - D inverse C)* D (A - D inverse C). The right side is positive semidefinite. The rectangular factors may be singular or zero; only D is required to be positive definite."),
        Item("rectangular_metric_trace_bound", "Rectangular trace bound",
            "Taking the real trace of the positive semidefinite remainder and using conjugate-transpose trace symmetry gives 2 Re Tr(A* C) <= Re Tr(A* D A) + Re Tr(C* D inverse C). The finite matrix statement includes zero-dimensional and singular rectangular-factor cases."),
        Item("metric_square", "Positive-metric Riccati remainder",
            "For Hermitian G and positive definite D, D + G D inverse G - G - G equals (D-G) D inverse (D-G), and this remainder is positive semidefinite. Positivity of D is the exact condition used for the actual inverse."),
        Item("covariance_metric_gap", "Covariance-metric gap",
            "For positive definite P,S,D, let G be the existing geometric mean of P inverse and S. Then GPG=S and the difference between the trace cost at D and the cost at G is exactly the real trace of the positive Riccati remainder multiplied by P, hence is nonnegative."),
        Item("covariance_metric_minimum", "Attained positive-metric minimum",
            "For positive definite P and S, the same G is an attained global minimizer over every positive definite competitor D of Re Tr(DP) + Re Tr(D inverse S), with value twice Re Tr(GP). The statement makes no claim about singular-metric inversion or singular minimizers."))));

    private static DocumentBlock Item(string name, string title, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
