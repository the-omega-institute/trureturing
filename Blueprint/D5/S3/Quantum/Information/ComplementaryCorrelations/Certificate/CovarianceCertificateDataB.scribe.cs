using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceCertificateDataBDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram data for Weyl weights (1, 0), (1, 1), and (1, 2).",
        H("Gram data for Weyl weights (1, 0), (1, 1), and (1, 2)"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedatab-block10"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataB.block10"),
                H("Weight (1, 0)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedatab-block11"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataB.block11"),
                H("Weight (1, 1)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedatab-block12"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataB.block12"),
                H("Weight (1, 2)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition))));
}
