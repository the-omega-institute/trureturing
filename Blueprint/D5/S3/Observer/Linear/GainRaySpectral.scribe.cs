using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRaySpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source-weighted golden spectrum", H("Source-weighted golden spectrum"), Blocks(
            Paragraph(Text("The native atom M is [0,1;1,1]. phi and psi are the expanding and contracting golden roots. spectralPlus=(M-psi I)/(phi-psi) and spectralMinus=(phi I-M)/(phi-psi). alpha(S) and eta(S) are their trace pairings with S. These definitions use the basis order of the actual acquisition matrix.")),
            Paragraph(Text("The source may have eta=0 or eta<0. Positivity is required only for alpha on legal sources. Every pure-M clock, including zero, uses the same literal trajectory and the same source.")),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayspectral-purem-spectral"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySpectral.pureM_spectral"),
                H("Source-weighted trace expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 2 by 2 auxiliary matrix S and every natural i, trace(acquisition(replicate i false) S) equals alpha(S) phi^i + eta(S) psi^i. This is the weighted trace, rather than the trace of M^i alone."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayspectral-legal-spectral-weights"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySpectral.legal_spectral_weights"),
                H("Legal source weights"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every P satisfying LegalSource P, alpha(P)>0 and alpha(P)+eta(P)=1. There is no sign or nonzero premise on eta(P)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayspectral-spectral-basis-weights"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySpectral.spectral_basis_weights"),
                H("Independent auxiliary source coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("alpha(spectralPlus)=1, eta(spectralPlus)=0, alpha(spectralMinus)=0 and eta(spectralMinus)=1. The two projectors are auxiliary matrices in universal linear identities; they need not be legal positive sources."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayspectral-purem-readat"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySpectral.pureM_readAt"),
                H("Literal clock expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d, original W:World d and natural n,i with i<=n, readAt W (replicate n false) i equals gain(d,W.coeff)(i) times [alpha(W.source) phi^i+eta(W.source) psi^i], plus W.drift. The coefficient vector, drift and clock are the original ones."))), DescribeRole.Theorem))));
}
