using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class ThetaDifferentialKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original theta differential kernel.",
        H("The original theta differential kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("thetaseries-local-majorant"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_local_majorant"),
                H("Local summable derivative majorants"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every natural k and every a > 0, pi times the weighted Gaussian series of degree k+2 at a is summable and bounds the absolute derivative terms at every t >= a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasderivat-thetaseries"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.hasDerivAt_thetaSeries"),
                H("Differentiating the actual series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every k and t > 0, thetaSeries k has derivative -pi times thetaSeries (k+2). The open ray above t/2 supplies the summable majorant required by the series differentiation theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thetaseries-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_zero"),
                H("The actual theta tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Romik (1.6) states the positive-index theta-tail identity for t > 0. Here thetaSeries 0 t equals (theta t - 1)/2; the Lean proof identifies theta with the even Hurwitz kernel at parameter zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omega-eq-series"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.omega_eq_series"),
                H("The original differential weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Romik (1.7) gives the positive-integer Gaussian series for omega at t > 0. Separating its two summable weights gives omega(t) = 2*pi^2*t^2*thetaSeries 4 t - 3*pi*t*thetaSeries 2 t; the repository proves this regrouping."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("romikphi-eq-differential"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_differential"),
                H("The theta differential identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every real x, romikPhi x = deriv (deriv psi) x - psi x / 4. Here psi(x)=exp(x/2)*(theta(exp(2*x))-1)/2 and romikPhi(x)=2*exp(x/2)*omega(exp(2*x)). Both differentiations have explicit locally summable bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psi-deriv-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_deriv_zero"),
                H("The modular boundary derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("The derivative of psi at zero is -1/4. Differentiating its modular reflection identity establishes this value without a mass-normalization assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("romikphi-even"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_even"),
                H("Evenness from modular differentiation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("Romik (1.9) states Phi(-x)=Phi(x) for every real x, with Phi defined without an absolute value in (1.8). The repository proof differentiates modular reflection: the defects in psi and its second derivative cancel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("romikphi-eq-source"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_source"),
                H("Identification on the whole real axis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For every real x, romikPhi x = sourceThetaKernel x. On the nonnegative axis the convergent series agree term by term; modular evenness extends the identification to negative x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psi-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_bounds"),
                H("Positive-half-line bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/romik2021orthogonal")),
                Blocks(Paragraph(Text("For x >= 0, both |psi x| and |psiFirst x| are at most sourceThetaKernel x. The weighted-series comparison supplies decay and integrability for integration by parts."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/SourceThetaMomentBounds"))
        ]));
}
