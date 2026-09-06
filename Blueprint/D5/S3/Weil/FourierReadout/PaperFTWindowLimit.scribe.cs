using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.FourierReadout;

internal sealed class PaperFTWindowLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From genuine varying operator-domain Rayleigh certificates and an explicit scaled rate, transfers the stated candidate Fourier limit to projectively normalized actual eigenvectors. The target limit and the candidate convergence remain explicit inputs; no Xi convergence is postulated or proved here.",
        H("PaperFTWindowLimit"),
        Blocks(
            Describe.Lean(DescribeId.Create("item-1"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/PaperFTWindowLimit.paperFT_window_uniform_error"), H("Uniform error from a measured L2 rate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual scaled Fourier differences converge uniformly to zero on the whole horizontal strip when the scaled window L2 error pays sqrt(2a)*exp(ba). Window radii and L2 spaces may vary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-2"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/PaperFTWindowLimit.paperFT_projective_uniform_error"), H("Uniform error from squared projective budgets"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transfers explicit squared error budgets through the same actual Fourier integral. The required weighted square-root rate is stated as a hypothesis; no rate is claimed for the arithmetic Weil family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("item-3"),
                DeclarationHandle.Create("D5/S3/Weil/FourierReadout/PaperFTWindowLimit.rayleigh_paperFT_uniform_limit"), H("Transfer the actual candidate Fourier limit"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From genuine varying operator-domain Rayleigh certificates and an explicit scaled rate, transfers the stated candidate Fourier limit to projectively normalized actual eigenvectors. The target limit and the candidate convergence remain explicit inputs; no Xi convergence is postulated or proved here."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate"))]));
}
