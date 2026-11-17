using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class GaussianCutoffDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/GaussianCutoff.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth frequency cutoffs and real inverse Fourier kernels.",
        H("Gaussian cutoff kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chi-nonneg"),
                DeclarationHandle.Create(Prefix + "chi_nonneg"),
                H("Nonnegative cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of the two smooth transition factors is nonnegative for every real parameter and frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-le-one"),
                DeclarationHandle.Create(Prefix + "chi_le_one"),
                H("Cutoff bounded by one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each transition factor lies between zero and one, so their product is at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-even"),
                DeclarationHandle.Create(Prefix + "chi_even"),
                H("Even cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Replacing the frequency by its negative exchanges the two transition factors and leaves the cutoff unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-eq-one"),
                DeclarationHandle.Create(Prefix + "chi_eq_one"),
                H("Central plateau"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive M, the cutoff equals one whenever the absolute frequency is at most M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-eq-zero"),
                DeclarationHandle.Create(Prefix + "chi_eq_zero"),
                H("Outer vanishing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive M, the cutoff vanishes whenever the absolute frequency is at least M plus M to the one-quarter power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-cont-diff"),
                DeclarationHandle.Create(Prefix + "chi_contDiff"),
                H("Smooth cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff is infinitely differentiable because its factors are smooth transitions composed with affine functions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-multiplier-cont-diff"),
                DeclarationHandle.Create(Prefix + "cutoff_multiplier_contDiff"),
                H("Smooth multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of the cutoff and exp(t squared divided by twice M squared) is infinitely differentiable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-multiplier-has-compact-support"),
                DeclarationHandle.Create(Prefix + "cutoff_multiplier_hasCompactSupport"),
                H("Compact frequency support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive M, the multiplier has compact support contained in [-(M+Delta), M+Delta], where Delta is M to the one-quarter power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-multiplier-even"),
                DeclarationHandle.Create(Prefix + "cutoff_multiplier_even"),
                H("Even multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both the Gaussian factor and the cutoff are even, so the multiplier is even."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-kernel-schwartz-coe"),
                DeclarationHandle.Create(Prefix + "cutoff_kernelSchwartz_coe"),
                H("Real Schwartz kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse Fourier transform of the normalized multiplier is a complex Schwartz function with zero imaginary part. Its value is the complexification of the real cutoff kernel. The normalized multiplier at xi is b evaluated at two pi times xi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-kernel-integrable"),
                DeclarationHandle.Create(Prefix + "cutoff_kernel_integrable"),
                H("Integrable kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real cutoff kernel is integrable for every M. For positive M it is the real part of a Schwartz function, and for nonpositive M it is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-kernel-cos"),
                DeclarationHandle.Create(Prefix + "cutoff_kernel_cos"),
                H("Cosine convolution identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For M at least one, convolution of the cutoff kernel with cos(gamma y) multiplies it by exp(gamma squared divided by twice M squared) times the cutoff at gamma. Fourier inversion with the normalization b(two pi xi) supplies the identity for every real gamma and y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-multiplier-bound"),
                DeclarationHandle.Create(Prefix + "cutoff_multiplier_bound"),
                H("Uniform Fourier multiplier bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For M at least one, the norm of the Mathlib Fourier transform of the complexified real kernel is at most exp(2) at every real frequency. Its transform is b(two pi xi), supported where the absolute angular frequency is at most M plus M to the one-quarter power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth-transition-derivatives-bounded"),
                DeclarationHandle.Create(Prefix + "smoothTransition_derivatives_bounded"),
                H("Uniform bounds on transition derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonnegative integer n, the absolute value of the nth derivative of the fixed smooth transition has a finite positive bound on the whole real line. Positive-order derivatives vanish outside the unit interval, and continuity bounds them on that interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-kernel-tail"),
                DeclarationHandle.Create(Prefix + "cutoff_kernel_tail"),
                H("Uniform kernel tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists a positive constant C independent of M such that, for every M at least one, the integral of the absolute cutoff kernel over absolute v at least one is at most C divided by M. Five differentiations give a multiplier derivative integral bounded by C divided by M: the central region contributes order M to the minus fourth power, and the two transition bands contribute order Delta to the minus fourth power. The Fourier derivative identity then gives fifth-power decay in v, whose tail is integrable."))),
                DescribeRole.Theorem))));
}
