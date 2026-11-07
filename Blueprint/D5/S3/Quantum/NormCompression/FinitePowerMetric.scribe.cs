using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class FinitePowerMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete symmetric inverse metric and actual spectral acceleration identity.",
        H("Full trace metric and acceleration"), Blocks(
            Describe.Lean(
                DescribeId.Create("finite-power-regularizedtable-affine"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerMetric.regularizedTable_affine"),
                H("Affine regularization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Regularization commutes with every affine combination whose coefficients sum to one."))), DescribeRole.Theorem),
            Paragraph(Text("The private metric suppliers retain both diagonal coordinates and the off diagonal direction. They are consumed directly by full cone concavity and by the fixed support radial Hessian kernel.")))));
}
