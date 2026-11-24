using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMeasurementCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The covariance estimate implies the standard-basis bound.",
        H("The covariance estimate implies the standard-basis bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-anchormeasurementcovariance-local-covariance-of-matrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementCovariance.localCovariance_of_matrix"),
                H("Local covariance of Hermitian observables"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Hilbert–Schmidt Cauchy–Schwarz controls the endpoint, midpoint and imaginary mixed moments of two Hermitian observables under a positive weight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormeasurementcovariance-acc23-of-raw-diagonal-circulant"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementCovariance.acc₂₃_of_raw_diagonal_circulant"),
                H("Standard-basis anchor convexity from qutrit covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Computational and Hadamard scores on the qubit reduce to centered Pauli Z and X. On the qutrit the scores are diagonal and circulant. The centered covariance estimate bounds the joint Simpson expression, yielding the anchor quadratic inequality."))), DescribeRole.Theorem))));
}
