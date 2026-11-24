using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate;

internal sealed class CovarianceWeylMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Hermitian qutrit Weyl representation.",
        H("The Hermitian qutrit Weyl representation"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-covarianceweylmatrix-reconstruct"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.reconstruct"),
                H("Weyl reconstruction of complex matrices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nine qutrit Weyl matrices form a trace-orthogonal coordinate system, giving reconstruction from the coefficient functional."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-covarianceweylmatrix-coordinate-star"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.coordinate_star"),
                H("Hermitian conjugacy of the coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Hermitian input, complex conjugation on a coordinate agrees with negation of its Weyl weight in the chosen phase convention."))), DescribeRole.Theorem))));
}
