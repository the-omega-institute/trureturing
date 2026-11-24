using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceCertificateDataADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram data for Weyl weights (0, 0), (0, 1), and (0, 2).",
        H("Gram data for Weyl weights (0, 0), (0, 1), and (0, 2)"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedataa-block00"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataA.block00"),
                H("Weight (0, 0)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedataa-block01"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataA.block01"),
                H("Weight (0, 1)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedataa-block02"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataA.block02"),
                H("Weight (0, 2)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition))));
}
