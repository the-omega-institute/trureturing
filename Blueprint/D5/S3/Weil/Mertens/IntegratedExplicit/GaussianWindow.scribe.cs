using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class GaussianWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-window complex Gaussian cancellation with explicit lower and upper tails.",
        H("Gaussian cancellation on a closed logarithmic window"),
        Blocks(
            Paragraph(Text("For w>0 the Gaussian measure has mean 2*w^2 and variance w^2/2. In this unit w=H+20. The complex frequency is -a+i*gamma. Every interval below is closed at both window endpoints.")),
            Paragraph(Text("The existing lower_tail, upper_tail and integral_three_intervals helpers are now public for direct reuse by SignedGaussianEndpoint.window_mass. Their proof bodies and hypotheses are unchanged; this visibility change adds no new Gaussian cancellation mathematics.")),
            Describe.Lean(
                DescribeId.Create("gaussianwindow-truncated-gaussian-cancellation"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/GaussianWindow.truncated_gaussian_cancellation"),
                H("The full transform and both discarded tails"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every H>=20000, 0<=a<=2 and abs(gamma)>=10, the norm of the complex exponential integral on [H,4*(H+20)^2] is at most exp(-25*(H+20)^2)+exp(-H^2)+exp(-4*(H+20)^2). The full Gaussian transform is imported through Mathlib complexMGF_id_gaussianReal. The lower-tail exponential tilt is -2, including negative arguments, and the upper tilt is +4. Their estimates and the exact three-interval decomposition prove the closed-window bound. SpectralAverage.averagedKernel_low_bound consumes this result."))),
                DescribeRole.Theorem),
            Paragraph(Text("The Gaussian transform and real exponential moments reuse Mathlib.Probability.Distributions.Gaussian.Real from the repository-pinned Mathlib under its existing license. The truncation and tail estimates are repository derivations; no literature priority is claimed. This unit has no actual-zero representation, correction assembly, mean-to-point inference or arithmetic endpoint assertion.")))));
}
