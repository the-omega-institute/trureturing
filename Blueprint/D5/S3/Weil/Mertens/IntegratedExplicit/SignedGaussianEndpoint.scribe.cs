using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class SignedGaussianEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete signed Gaussian endpoint",
        H("A complete signed Gaussian endpoint"),
        Blocks(
            Paragraph(Text("GaussianWindow, CountableResolvent and SpectralAverage are the sole owners of the Gaussian, complete countable spectrum, resolvent and complex average estimate. This module adds the bounded real correction, the closed-window weighted mass and the strict mean-to-point argument. Every supplied spectral occurrence is retained.")),
            Paragraph(Text("For C measurable on the positive half-line with 0<=C(v)<=1, signedQ(v)=-Re(spectralSeries(v))+(C(v)-log(2*pi))*exp(-v). Its W-weighted tail is signedG. The correction average is at most 8*exp(-H)/H. Combining the existing spectral average gives the loose bound 1000*exp(-H)/H, with all integrability proved.")),
            Paragraph(Text("For H>=20000, the Gaussian has at least half its mass in [H,4*(H+20)^2], and the integral of R over that window is at least 1/(8*(H+20)^2). The cubic Taylor term proves the strict scalar gap needed to force a point with signedG(y)/R(y)>-1/(2*sqrt(A)) when A>=10000 and A<=exp(H). This is the new signed endpoint step, not a restatement of old positive-peak mathematics. These are uniform analytic proofs, not certified finite instances or an assertion of literature novelty.")),
            Describe.Lean(
                DescribeId.Create("signedgaussianendpoint-full-summed-average-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.full_summed_average_bound"),
                H("A complete signed Gaussian endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full signed mean bound follows from canonical spectral cancellation plus the bounded correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signedgaussianendpoint-signedg-window-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.signedG_window_integrable"),
                H("A complete signed Gaussian endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed tail is integrable on the closed Gaussian window; this is consumed by the actual-source instantiation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signedgaussianendpoint-endpoint-of-complete-representation"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.endpoint_of_complete_representation"),
                H("A complete signed Gaussian endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An exact complete representation q(v)=signedQ(v) on v>=H yields a strict signed endpoint at some y in the original closed window."))),
                DescribeRole.Theorem))));
}
