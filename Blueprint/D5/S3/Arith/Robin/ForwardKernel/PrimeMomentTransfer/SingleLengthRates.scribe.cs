using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SingleLengthRatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit errors in single-length prime moments decay uniformly on polynomial length bands.",
        H("Uniform single-length rates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cumulative-sampling-rate"),
                DeclarationHandle.Create(Prefix + "cumulativeSamplingRate"),
                H("Cumulative sampling rate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The relative cumulative sampling envelope is sqrt(log Y/v) plus (log Y/v)^(k/2) plus (v log Y)^(k/2)/Y. The last summand bounds the terminal fractional cell."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ms-error-uniform"),
                DeclarationHandle.Create(Prefix + "ms_error_uniform"),
                H("Uniform moment error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For moment order two or four and positive alpha less than beta less than one quarter, the full explicit Montgomery–Soundararajan error is little-o of Y v^(k/2) log(Y/v)^(k/2) uniformly on the polynomial band, provided epsilon is positive and less than one half minus twice beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sampling-uniform"),
                DeclarationHandle.Create(Prefix + "sampling_uniform"),
                H("Uniform sampling envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For moment order two or four and positive alpha less than beta less than one quarter, the sum of sqrt(log Y/v), (log Y/v)^(k/2), and (v log Y)^(k/2)/Y tends to zero uniformly for Y^alpha at most v at most Y^beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("main-errors-uniform"),
                DeclarationHandle.Create(Prefix + "main_errors_uniform"),
                H("Uniform rounding error in the main term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For moment order two or four and positive alpha less than beta less than one quarter, replacing the cutoff and length by their natural floors changes the main term by little-o of Y v^(k/2) log(Y/v)^(k/2), uniformly on the polynomial band."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-main-uniform"),
                DeclarationHandle.Create(Prefix + "second_main_uniform"),
                H("Normalized second main term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive alpha less than beta less than one, the second main term divided by Y v log(Y/v) tends to one uniformly for Y^alpha at most v at most Y^beta. The exact logarithmic integral leaves a remainder bounded by a constant times Y, and log(Y/v) is at least (1-beta) log Y."))),
                DescribeRole.Theorem))));
}
