using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceMatrixAdapterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The covariance inequality for actual qutrit observables.",
        H("The covariance inequality for actual qutrit observables"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covariancematrixadapter-physical-possemidef"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.physical_posSemidef"),
                H("Compression to two physical observables"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A diagonal and a circulant Hermitian observable expand in the two Weyl subspaces. Their covariance matrix is a compression of the polynomial Gram matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-covariancematrixadapter-bob-raw-covariance"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.bob_raw_covariance"),
                H("The bound at the actual qutrit square root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The determinant inequality of the two-by-two positive covariance matrix gives the squared real cross term plus nine quarters of the squared imaginary cross term. Taking the actual square root provides the raw bound for every positive semidefinite trace-one qutrit state."))), DescribeRole.Theorem))));
}
