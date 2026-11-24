using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact covariance certificate.",
        H("The exact covariance certificate"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancecertificate-ldl-entries"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.ldl_entries"),
                H("Shifted Gram factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every block has the displayed LDL factorization after subtracting one fifth of the identity. The arithmetic is exact in the rational quadratic coefficient ring."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-covariancecertificate-coefficient-equality"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.coefficient_equality"),
                H("Equality of quartic coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The checker compares every entry of the target covariance matrix with the sum of the Weyl-weight Gram forms."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-covariancecertificate-covariance-possemidef"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_posSemidef"),
                H("Positive semidefiniteness on Hermitian coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shifted factorizations and positive pivots yield nonnegative Gram forms. The coefficient equality identifies their sum with the covariance matrix for every conjugation-compatible Weyl coefficient vector."))), DescribeRole.Theorem))));
}
