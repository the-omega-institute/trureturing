using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeSharedRootFeedbackDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Poisson windows, rectangle masses, and shared calibration produce lower bounds for the complete native reference variance. Classical Poisson and hypergeometric estimates are documented in Library/Estimation; the combined variance and calibration contracts are repository-derived.",
        H("Native shared-root variance and calibration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("root-box-of-residual"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.root_box_of_residual"),
                H("Root box from a center residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every F : Real -> Real and real q,x0,x,d,a,b, assume d>0, a>0, StrictMono F, ContinuousOn F on [x0-d,x0+d], DifferentiableOn Real F in that interval's interior, and a<=deriv F u at every interior u. If F x=q, |F x0-q|<=b and b<=a*d, then |x-x0|<=d and a*|x-x0|<=b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-root-central-bootstrap"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.shared_root_central_bootstrap"),
                H("Central shared-root bootstrap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite index type iota, outside : iota -> Real and real r,epsilon,N,R,U,q,t,t0,x0,x,w, assume N>0, every cellCounts N R U t j is nonnegative, |t-t0|<=w, calibratedMean outside r epsilon N R U t0 x0=q and calibratedMean outside r epsilon N R U t x=q. Let V0=calibratedVariance outside r epsilon N R U t0 x0. Assume w<V0 and 2*w<=(V0-w)*log(2)/2. Then |x-x0|<=log(2), |x-x0|<=4*w/(V0-w), and (V0-w)/2<=calibratedVariance outside r epsilon N R U t x<=2*(V0+w)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compensated-feedback-bounds"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_bounds"),
                H("Compensated feedback bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all real r,epsilon,x,B,D,d,a,b,X, assume 0<a<=D<=b, B>=0, d>=0, checkerboard r epsilon x<=-d, |x|<=X and |x|<=log(2). Then Real.sigmoid x-1/2-B*Real.sigmoid x*(1-Real.sigmoid x)*checkerboard r epsilon x/D lies between B*d/(8*b)-X/4 and X/4+B/(2*a)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compensated-feedback-box"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_box"),
                H("Uniform compensated feedback box"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r with 0<r<1, there exist real d,delta with d>0, delta>0 and delta<=log(2) such that, for all real epsilon,x satisfying |epsilon|<delta and |x|<delta, checkerboard r epsilon x<=-d. The same d and delta work for every epsilon and x in this box."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-variance-count-window"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_count_window"),
                H("Reference variance on a count window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite count window below the calibration threshold contributes a lower bound to the complete reference variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signal-rectangle-mass-lower"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.signal_rectangle_mass_lower"),
                H("Signal rectangle mass lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite signal rectangle inside the square-root windows has an explicit lower bound for its native reference mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-variance-window-lower"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_window_lower"),
                H("Reference variance on a signal window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite signal square-root window supplies a complete reference-variance lower bound while retaining the remaining signal and background counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-linear-variance-lower"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_linear_variance_lower"),
                H("Linear reference variance lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A concrete lower-left and upper-right count box yields a linear lower bound for the complete reference variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("floored-signal-reference-mass"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.floored_signal_reference_mass"),
                H("Floored signal reference mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native signal reference mass has a uniform floor under the stated compensated-parameter and scale conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-calibration-root-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_root_budget"),
                H("Native calibration root budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a compensation parameter in the unit interval, the native calibration root admits the displayed positive budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-calibration-window-root-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_window_root_budget"),
                H("Native calibration window budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The calibrated root remains within the stated window with the displayed budget under the same parameter range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("anchored-central-shared-calibration"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.anchored_central_shared_calibration"),
                H("Anchored central shared calibration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full native root anchor drives one shared central calibration curve and its positive compensated response."))),
                DescribeRole.Theorem)
        )));
}
