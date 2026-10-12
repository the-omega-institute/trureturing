using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeSharedRootFeedbackDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Poisson windows, rectangle masses, and shared calibration produce lower bounds for the complete native reference variance. Classical Poisson and hypergeometric estimates are documented in Library/Estimation; the combined variance and calibration contracts are repository-derived.",
        H("Native shared-root variance and calibration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reference-variance-count-window"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeReferenceVarianceBounds.reference_variance_count_window"),
                H("Reference variance on a count window"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite count window below the calibration threshold contributes a lower bound to the complete reference variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signal-rectangle-mass-lower"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeRectangleReferenceMass.signal_rectangle_mass_lower"),
                H("Signal rectangle mass lower bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite signal rectangle inside the square-root windows has an explicit lower bound for its native reference mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-variance-window-lower"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeReferenceVarianceBounds.reference_variance_window_lower"),
                H("Reference variance on a signal window"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite signal square-root window supplies a complete reference-variance lower bound while retaining the remaining signal and background counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-linear-variance-lower"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeReferenceVarianceBounds.reference_linear_variance_lower"),
                H("Linear reference variance lower bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A concrete lower-left and upper-right count box yields a linear lower bound for the complete reference variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("floored-signal-reference-mass"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeRectangleReferenceMass.floored_signal_reference_mass"),
                H("Floored signal reference mass"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native signal reference mass has a uniform floor under the stated compensated-parameter and scale conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-calibration-root-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeCalibrationRootBudgets.native_calibration_root_budget"),
                H("Native calibration root budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a compensation parameter in the unit interval, the native calibration root admits the displayed positive budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-calibration-window-root-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeCalibrationRootBudgets.native_calibration_window_root_budget"),
                H("Native calibration window budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The calibrated root remains within the stated window with the displayed budget under the same parameter range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("anchored-central-shared-calibration"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.NativeSharedRootFeedback.anchored_central_shared_calibration"),
                H("Anchored central shared calibration"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full native root anchor drives one shared central calibration curve and its positive compensated response."))),
                DescribeRole.Theorem)
        )));
}
