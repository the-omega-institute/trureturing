using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class XiThetaTransformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The theta transform and completed zeta.",
        H("The theta transform and completed zeta"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integrable-tilted-gaussian"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.integrable_tilted_gaussian"),
                H("Gaussian integrability under exponential tilts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every real b, exp(-x^2+b*x) is integrable on the real line, by the complex Gaussian integral API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.ray_integrable"),
                H("Absolute convergence from the kernel bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("If a continuous real function f satisfies |f(x)| <= sourceThetaKernel(x) for all x >= 0, then f(x)*exp(w*x) is integrable on the positive half-line for every complex w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-tendsto"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.ray_tendsto"),
                H("The endpoint at infinity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Under the same pointwise domination, f(x)*exp(w*x) tends to zero as x tends to positive infinity, for every complex w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psi-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.psi_integrable"),
                H("Convergence for the theta tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, psi(x)*exp(w*x) is absolutely integrable on x > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psifirst-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.psiFirst_integrable"),
                H("Convergence for the first derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, psiFirst(x)*exp(w*x) is absolutely integrable on x > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-halfline-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.kernel_halfline_integral"),
                H("Two integrations by parts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, the integral over x > 0 of sourceThetaKernel(x)*exp(w*x) equals 1/4 + w*psi(0) + (w^2-1/4)*thetaLaplace(w). All endpoint limits and the integrability of each derivative term are proved from the actual theta tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thetamellin-eq-completed"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_eq_completed"),
                H("The symmetric Mellin integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex s, the literal symmetric theta-tail Mellin integral thetaMellin(s) equals completedRiemannZeta-zero(s). Additive cancellation of the two explicit pole terms in the public reconstruction proves this at s=0 and s=1 as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-fourier-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_integrable"),
                H("All-complex Fourier integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex z, sourceThetaKernel(x)*exp(i*z*x) is absolutely integrable on the real line. The Gaussian bound absorbs every complex exponential tilt."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thetamellin-center"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_center"),
                H("The logarithmic substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, thetaMellin(1/2+w)=2*(thetaLaplace(w)+thetaLaplace(-w)). The proof uses t=exp(2*x) with the exact factor two and justifies splitting the two convergent half-line integrals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-fourier-eq-xi"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_eq_xi"),
                H("The all-complex transform to xi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex z, the integral over the real line of sourceThetaKernel(x)*exp(i*z*x) equals xiReading(1/2+i*z). Two integrations by parts on the positive half-line, reflection, and the symmetric Mellin identity prove the result. No division by s*(s-1) occurs, so z=0 and z=plus or minus i/2 are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-coefficient-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_coefficient_zero"),
                H("The constant coefficient is one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("The literal normalized theta coefficient sourceThetaCoefficient 0 equals one. The all-complex Fourier identity at zero identifies the total mass with the real xi value at the center, and positivity of the actual kernel proves this denominator is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-theta-normalized"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_normalized"),
                H("Unconditional normalization and positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("The real xi value at 1/2 is the integral of sourceThetaKernel and is strictly positive; sourceThetaDensity has integral one; every sourceThetaCoefficient k is strictly positive. The existing normalization theorem is applied with its constant-coefficient premise now proved."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/CompletedZetaMellinReconstruction"))
        ]));
}
