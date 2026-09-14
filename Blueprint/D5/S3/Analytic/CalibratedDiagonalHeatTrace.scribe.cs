using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class CalibratedDiagonalHeatTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/CalibratedDiagonalHeatTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A calibrated noisy complete heat trace excludes the actual low spectrum of a finite diagonal matrix.",
        H("Calibrated Diagonal Heat Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("calibrated-diagonal-heat-trace-definition"),
                DeclarationHandle.Create(Prefix + "diagonalHeatTrace"),
                H("Actual matrix heat trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Matrix.trace of NormedSpace.exp of the time-scaled real diagonal energy matrix. This is not a freely supplied correlation function."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibrated-diagonal-heat-trace-identity"),
                DeclarationHandle.Create(Prefix + "diagonalHeatTrace_eq"),
                H("Matrix exponential identification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pinned Mathlib matrix-exponential identities identify the actual heat trace with the finite sum of scalar Laplace kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibrated-diagonal-heat-trace-spectrum-exclusion"),
                DeclarationHandle.Create(Prefix + "calibrated_diagonal_spectrum_exclusion"),
                H("Single-time noisy spectral exclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative diagonal energies bounded by 2r, a complete trace observation y at log(2)/r with absolute error delta and y+delta < (dimension+1)/4 proves that the actual Mathlib spectrum lies above r. The bound uses every mode, a strict margin, and the upper-band calibration. It does not pass to a quantum field theory or an infinite-dimensional limit."))),
                DescribeRole.Theorem))));
}
