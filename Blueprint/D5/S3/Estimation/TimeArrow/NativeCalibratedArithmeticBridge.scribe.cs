using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeCalibratedArithmeticBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete reference count law has mean calibration equal to the support size. The actual full-row posterior uses the same calibration and the same minimal environment when its phase event is bounded by a lattice event.",
        H("Full native posterior and calibration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reference-calibration-mean-variance"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge.NativeReferenceCalibration.reference_calibration_mean_variance"),
                H("Reference calibration mean variance"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete reference mean equals the support size, and its variance is the displayed signal-row complement sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-reference-calibration-deviation"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge.NativeReferenceCalibration.native_reference_calibration_deviation"),
                H("Native reference calibration deviation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full weighted row moments jointly bound the actual mean-calibration and variance deviations from the complete reference quantities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-environment-mean-variance"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge.NativeCalibratedArithmeticBridge.native_environment_mean_variance"),
                H("Native environment mean variance"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full-row Bernoulli mean and variance are represented by the same outside counts and four-cell calibration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-posterior-central-kernel-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge.NativeCalibratedArithmeticBridge.native_posterior_central_kernel_bound"),
                H("Native posterior central kernel bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original posterior phase event is dominated by a count tail and one central lattice event using the same calibration root and variance."))),
                DescribeRole.Theorem)
        )));
}
