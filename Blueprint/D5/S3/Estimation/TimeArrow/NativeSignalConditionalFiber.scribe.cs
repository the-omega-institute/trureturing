using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeSignalConditionalFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collapsed native histories admit a uniform law on their erased signal labels. The same finite row data support a logistic calibration curve, its scalar variance estimates, and the original count and population floors.",
        H("Native signal fibers and common calibration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-signal-assignment-law"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.NativeSignalConditionalFiber.native_signal_assignment_law"),
                H("Native signal assignment law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every event of erased signal labels has its exact conditional mass under the original pair or path experiment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-calibration-curve"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.SharedRectangleCalibration.shared_calibration_curve"),
                H("Shared calibration curve"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One root function solves the full calibration throughout the feasible open interval; local implicit roots agree with it by uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-fiber-variance-bounds"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.RectangleCalibrationBounds.central_fiber_variance_bounds"),
                H("Central fiber variance bounds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common odds tilt and a controlled change in the four-cell histogram bound the variance of the same complete calibration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-rounding"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.NativeGrowthRounding.central_rounding"),
                H("Central rounding"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two original central counts retain their exact sum and a floor error between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-rounding"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.NativeGrowthRounding.center_rounding"),
                H("Center rounding"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The central score lies between the information-rate score and that score minus one log-odds increment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("information-rate-bounds"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.NativeGrowthRounding.information_rate_bounds"),
                H("Information rate bounds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed amplitude strictly between zero and one gives an information rate strictly between zero and log two."))),
                DescribeRole.Theorem)
        )));
}
