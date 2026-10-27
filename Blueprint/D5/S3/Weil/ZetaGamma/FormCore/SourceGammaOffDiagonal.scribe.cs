using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class SourceGammaOffDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original L1 half-line input pays the reflected cross before inversion.",
        H("The actual reflected Fourier kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-gamma-off-diagonal-actual-l1-reflected-unitary-cross-kernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_l1_reflected_unitary_cross_kernel"),
                H("The reflected cross uses the sum of the source coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex half-line L1 source u and complex full-line L1 multiplier p, the actual reflected unitary Fourier cross is integrable. Its integral equals the actual double half-line kernel integral. The operator kernel carries 1/(2*pi); its argument is s+t. These absolute-domain proofs precede Fubini."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-gamma-off-diagonal-actual-resolvent-inverse-kernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_inverse_kernel"),
                H("The actual resolvent kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and every real z, the actual L1 inverse multiplier kernel of 1/(xi^2+a^2) equals exp(-a*abs(z))/(2*a), with the original multiplier integrability retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-gamma-off-diagonal-actual-resolvent-reflected-cross-laplace-square"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_reflected_cross_laplace_square"),
                H("The original source Laplace square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and every complex half-line L1 input u, the actual reflected resolvent cross equals normSq(Laplace(a,u))/(2*a). Both the actual Laplace and spectral-product domains are proved in the same statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-gamma-off-diagonal-actual-resonant-inverse-kernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_inverse_kernel"),
                H("The double pole retains its sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0, the actual multiplier xi^2/[a*(xi^2+a^2)^2] has inverse kernel exp(-a*abs(z))*(1-a*abs(z))/(4*a^2). The proof computes the genuine exponential self-convolution. This signed kernel is retained, including its change of sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-gamma-off-diagonal-actual-resonant-reflected-cross-kernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_kernel"),
                H("The actual resonant reflected double integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and the original arbitrary complex L1 source, the resonant reflected spectral cross and its actual double half-line kernel integral agree. The sum s+t and signed kernel remain literal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-gamma-off-diagonal-actual-resonant-reflected-cross-laplace-moment"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_laplace_moment"),
                H("The resonant first moment is explicit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0, the real resonant cross is normSq(Laplace(a,u))/(4*a^2) minus Re(conj(Laplace(a,u))*FirstMoment(a,u))/(2*a). The genuine first moment is integrable. The mixed term is retained in the later actual Gamma calculation; the kernel suppliers alone imply no energy positivity."))),
                DescribeRole.Theorem))));
}
