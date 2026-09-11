using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class ThetaHalfLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta integrals on the positive half-line.",
        H("Theta integrals on the positive half-line"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integrable-tilted-gaussian"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaHalfLine.integrable_tilted_gaussian"),
                H("Gaussian integrability under exponential tilts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every real b, exp(-x^2+b*x) is integrable on the real line, by the complex Gaussian integral API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaHalfLine.ray_integrable"),
                H("Absolute convergence from the kernel bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("If a continuous real function f satisfies |f(x)| <= sourceThetaKernel(x) for all x >= 0, then f(x)*exp(w*x) is integrable on the positive half-line for every complex w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-tendsto"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaHalfLine.ray_tendsto"),
                H("The endpoint at infinity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Under the same pointwise domination, f(x)*exp(w*x) tends to zero as x tends to positive infinity, for every complex w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psi-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaHalfLine.psi_integrable"),
                H("Convergence for the theta tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, psi(x)*exp(w*x) is absolutely integrable on x > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psifirst-integrable"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaHalfLine.psiFirst_integrable"),
                H("Convergence for the first derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, psiFirst(x)*exp(w*x) is absolutely integrable on x > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-halfline-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaHalfLine.kernel_halfline_integral"),
                H("Two integrations by parts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every complex w, the integral over x > 0 of sourceThetaKernel(x)*exp(w*x) equals 1/4 + w*psi(0) + (w^2-1/4)*thetaLaplace(w). All endpoint limits and the integrability of each derivative term are proved from the actual theta tail."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel"))
        ]));
}
