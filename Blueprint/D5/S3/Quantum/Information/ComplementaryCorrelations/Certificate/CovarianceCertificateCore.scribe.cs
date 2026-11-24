using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceCertificateCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial reflection in Weyl coordinates.",
        H("Exact polynomial reflection in Weyl coordinates"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancecertificatecore-eval-eq-of-normalize-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateCore.eval_eq_of_normalize_eq"),
                H("Soundness of polynomial normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sorting each commutative monomial and collecting its rational quadratic-algebra coefficients preserves complex evaluation. Equality of normalized coefficient lists therefore implies equality of the evaluated polynomials."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatecore-eval-targetterms"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateCore.eval_targetTerms"),
                H("Evaluation of the covariance entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Weyl trace coefficients turn the symbolic target terms into the entries of the covariance matrix."))), DescribeRole.Theorem))));
}
