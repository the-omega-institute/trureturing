using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeAnchoredSmallBallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native anchored posterior is controlled by a calibrated curve, a shared root, and finite occupancy budgets. The analytic inputs are the repository Library/Estimation notes on Poisson, hypergeometric, and small-ball estimates; the assembled statements are repository-derived.",
        H("Native anchored small-ball geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-certified-curve-small-ball"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall.NativeAnchoredSmallBall.native_certified_curve_small_ball"),
                H("Certified native curve small-ball"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A calibrated curve certificate supplies the full posterior approximation while preserving the original minimal conditioning environment and its tails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-anchored-posterior-small-ball"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall.NativeAnchoredSmallBall.native_anchored_posterior_small_ball"),
                H("Anchored posterior small-ball"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the native curve, slope, occupancy, and scale hypotheses, the conditional fiber mass of the integer small-ball event obeys the explicit bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-cell-occupancy-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall.NativeRectangleOccupancy.native_cell_occupancy_budget"),
                H("Native cell occupancy budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native calibration cells satisfy the stated occupancy budget for every compensation parameter in the unit interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-five-cell-occupancy-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall.NativeRectangleOccupancy.native_five_cell_occupancy_budget"),
                H("Five-cell occupancy budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The five-cell native occupancy count satisfies the corresponding uniform budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-signal-background-occupancy"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall.NativeRectangleOccupancy.native_signal_background_occupancy"),
                H("Signal and background occupancy"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native signal and background cells obey the displayed joint occupancy relations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-signal-geometry-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall.NativeRectangleGeometry.native_signal_geometry_budget"),
                H("Native signal geometry budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native signal rectangle geometry is bounded by the explicit calibration budget under the stated parameter range."))),
                DescribeRole.Theorem)
        )));
}
