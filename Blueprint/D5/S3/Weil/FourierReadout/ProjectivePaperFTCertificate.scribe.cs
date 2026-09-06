using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.FourierReadout;

internal sealed class ProjectivePaperFTCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derives nonzero candidate overlap, candidate-adapted Fourier error, the uniform strip bound and an actual eigenvector nonvanishing test from genuine complex operator-domain inputs. No Fourier identity or projective error bound is supplied as a premise.",
        H("ProjectivePaperFTCertificate"),
        Blocks(
            Describe.Lean(DescribeId.Create("item-1"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate.paperFT_projective_squared_error"), H("Candidate-adapted actual Fourier error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumes the existing projective error theorem with the constructed Fourier representer. Only the candidate-orthogonal part of the actual readout contributes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-2"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate.paperFT_robust_nonvanishing_iff"), H("Sharp Fourier nonvanishing criterion"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transports the existing least-energy cancellation result to the paperFT integral. Sharpness is for the entire closed orthogonal L2 ball, not the eigenmode errors of a particular arithmetic operator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-3"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate.paperFT_real_robust_nonvanishing_iff"), H("Explicit real-frequency threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combines the sharp condition with the exact kernel norm 2a. No kernel quadrature, parity or smoothness assumption is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-4"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate.paperFT_projective_strip_bound"), H("Uniform strip error budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A squared L2 error budget yields sqrt(2a)*exp(ba)*sqrt(delta) for the actual Fourier error on the complete horizontal strip."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-5"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate.rayleigh_paperFT_certificate"), H("Actual Rayleigh-to-Fourier certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives nonzero candidate overlap, candidate-adapted Fourier error, the uniform strip bound and an actual eigenvector nonvanishing test from genuine complex operator-domain inputs. No Fourier identity or projective error bound is supplied as a premise."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/FourierReadout/WindowPaperFTReadout")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/ProjectiveReadoutSharpness"))]));
}
