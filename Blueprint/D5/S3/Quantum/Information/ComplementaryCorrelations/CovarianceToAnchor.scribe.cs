using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class CovarianceToAnchorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bloch-vector inequality for the Simpson estimate.",
        H("Bloch-vector inequality for the Simpson estimate"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancetoanchor-simpson-cubic-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchor.simpson_cubic_nonneg"),
                H("A nonnegative scalar cubic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The covariance bound and the endpoint and midpoint moment inequalities imply nonnegativity through bounds on the Bernstein coefficients over the unit interval."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-covariancetoanchor-simpson-gap-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchor.simpson_gap_nonneg"),
                H("Nonnegativity of the Bloch-oriented Simpson gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar cubic controls the diagonal and cross terms for each admissible Bloch vector, including arbitrary qubit orientation."))), DescribeRole.Theorem))));
}
