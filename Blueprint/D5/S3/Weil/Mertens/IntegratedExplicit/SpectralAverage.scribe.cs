using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class SpectralAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete countable spectral tail satisfies an explicit Gaussian-window average estimate.",
        H("A Gaussian average of the complete signed spectrum"),
        Blocks(
            Paragraph(Text("Let S be the complete countable spectrum described in CountableResolvent and let H>=20000. The averaging measure is the Gaussian of mean 2*(H+20)^2 and variance (H+20)^2/2 restricted to the closed window [H,4*(H+20)^2]. The conclusion bounds the norm of the complex average, retaining every supplied occurrence and both imaginary signs.")),
            Describe.Lean(
                DescribeId.Create("spectralaverage-spectral-average-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/SpectralAverage.spectral_average_bound"),
                H("Low and high frequencies pay for the average"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The average norm is at most cancellationError(H)/6+(7/5)*exp(-H)/H, where cancellationError(H)=exp(-25*(H+20)^2)+exp(-H^2)+exp(-4*(H+20)^2). For 0<s<=1, truncated_gaussian_cancellation applies to a=s+1-Re(z) and gives a per-mode contribution cancellationError(H)/12. For s>1, the exact positive half-axis moment exp(-H)*(2/H+3/H^2+2/H^3), proved with its boundary limit, gives (7/10)*exp(-H)/H. The high-frequency part is never extended through negative Gaussian arguments. Fubini, the countable resolvent identity and dominated convergence combine these estimates, and only then use the total coefficient norm at most 2. No mean or integral budget is a premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is an analytic estimate for all spectra satisfying the explicit hypotheses, not a finite computation or a numerical reduction with an unpaid certificate. The substantive mechanism is the consumed closed-window cancellation plus the dominated countable resolvent exchange and low/high frequency split. Supporting moment, integrability and norm helpers serve this single proof path.")),
            Paragraph(Text("This module does not identify the abstract series with actual zeta zeros, add the elementary bounded correction, take a mean to obtain a point, or prove an arithmetic Q or Robin5040 statement. No RH or literature-priority claim is made.")))));
}
