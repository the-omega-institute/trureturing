using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceCertificateDataCDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram data for Weyl weights (2, 0), (2, 1), and (2, 2).",
        H("Gram data for Weyl weights (2, 0), (2, 1), and (2, 2)"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedatac-block20"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataC.block20"),
                H("Weight (2, 0)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedatac-block21"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataC.block21"),
                H("Weight (2, 1)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qian-covariancecertificatedatac-block22"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataC.block22"),
                H("Weight (2, 2)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This block gives the exact basis columns, Gram entries, lower triangular entries and rational pivots used in the shifted factorization."))), DescribeRole.Definition))));
}
