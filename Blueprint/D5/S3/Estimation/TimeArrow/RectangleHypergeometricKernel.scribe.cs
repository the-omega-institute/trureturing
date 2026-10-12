using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class RectangleHypergeometricKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive and negative occupation counts come from one native history. Forgetting the labelled rectangle margins gives their conditional hypergeometric intersection law. Stirling envelopes provide the classical factorial estimates used by later bounds.",
        H("Native labelled histograms and rectangle kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-joint-row-histogram-law"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel.NativeSignalConditionalFiber.native_joint_row_histogram_law"),
                H("Native joint row histogram law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete labelled histogram event has the exact mass of the corresponding two occupation-word sectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-margin-rectangle-hypergeometric-law"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel.RectangleHypergeometricKernel.native_margin_rectangle_hypergeometric_law"),
                H("Native margin rectangle hypergeometric law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After conditioning on numeric margins and the labelled outside counts, the actual rectangle intersection count has the same hypergeometric kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-calibration-counts-margins"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel.SharedRectangleCalibration.native_calibration_counts_margins"),
                H("Native calibration counts margins"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four calibration-cell counts recover the rectangle size, its two margins, and its lower-left count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-factorial-envelopes"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel.NativeCalibratedArithmeticBridge.log_factorial_envelopes"),
                H("Log factorial envelopes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Classical Stirling inequalities place log factorial between the displayed two scalar envelopes."))),
                DescribeRole.Theorem)
        )));
}
