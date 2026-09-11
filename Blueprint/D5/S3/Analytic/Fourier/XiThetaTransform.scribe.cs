using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class XiThetaTransformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The theta transform and completed zeta.",
        H("The theta transform and completed zeta"),
        Blocks(
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
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Fourier/ThetaHalfLine")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/CompletedZetaMellinReconstruction"))
        ]));
}
