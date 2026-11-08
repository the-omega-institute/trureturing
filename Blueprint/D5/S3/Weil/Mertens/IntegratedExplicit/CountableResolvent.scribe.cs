using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CountableResolventDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dominated complete-series exchange through the positive W-weighted Laplace resolvent.",
        H("Countable W-weighted spectral resolvents"),
        Blocks(
            Paragraph(Text("CountableSpectrum carries zero and coefficient sequences indexed by all natural numbers. Each zero satisfies 0<Re(z)<1 and abs(Im(z))>10. The coefficient norms are summable and their total is at most 2. No beta cap below 1, symmetry quotient, finite truncation, integral budget or signed-tail hypothesis is included.")),
            Paragraph(Text("The literal spectral tail is the integral over v>y of W(v) times the complete sum of c_k*exp((z_k-1)*v), where W(v)=(v+2)/v^3. The resolvent denominator is s+1-z, its numerator is s*(1+s), and each mode integrates the resolvent kernel over s>0. R(v)=(v+1)/v^2 supplies integrability of W through its derivative and its limit at infinity.")),
            Paragraph(Text("The same owner now exposes the consumed R weight, spectral series and W-tail integrability. W_tail proves its exact mass R(y), and spectral_weighted_integrable proves W times the full series is L1 by uniform convergence and coefficient-norm domination. These consumed support facts serve SignedGaussianEndpoint; no second spectrum or resolvent is introduced.")),
            Describe.Lean(
                DescribeId.Create("countableresolvent-spectral-weighted-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.spectral_weighted_integrable"),
                H("The complete weighted series is integrable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complete CountableSpectrum and y>0, W(v)*spectralSeries(S,v) is L1 on (y,infinity). Coefficient-norm domination and uniform convergence justify the complete series, and the W-tail majorant pays the integral. This consumed support is owned here and used by the signed correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countableresolvent-w-tail"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.W_tail"),
                H("The exact positive weight mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every y>0, integral_(y,infinity) W(v)=R(y). The existing derivative R'=-W and R(infinity)=0 pay the exact improper endpoint. The signed correction uses this mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countableresolvent-countable-resolvent-identity"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.countable_resolvent_identity"),
                H("The complete countable resolvent identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive y, spectralTail(S,y) equals the complete sum of c_k*resolventMode(z_k,y). The common positive s,v kernel is proved product integrable before Fubini. Per-mode integration then gives the literal resolvent, and dominated convergence with bound norm(c_k)*W(v) exchanges the whole series with the weighted tail. SpectralAverage.spectral_average_bound uses the identity to obtain its pointwise HasSum; the identity is on the active average proof path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countableresolvent-laplace-weight-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplace_weight_integrable"),
                H("Integrable positive Laplace weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every y>0, s*(1+s)*exp(-s*y) is integrable on s>0. The proof directly reuses TwoScaleEndpointMoments.exponential_moment at rate y for n=1,2. Its integrability and equality components supply the private real moments and exact W moment. SpectralAverage.window_kernel_integrable and high_tail_integrable require this fact."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-laplace-polynomial-nonneg"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplacePolynomial_nonneg"),
                H("Nonnegative Laplace polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial s*(1+s) is nonnegative for s>=0. This consumed algebraic helper is used by the product majorants and the low and high frequency bounds in SpectralAverage."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-w-antitone"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.W_antitone"),
                H("The W weight decreases on the positive axis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<x<=y, W(y)<=W(x). Its reciprocal-power proof supplies the uniform window majorant in spectral_average_bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-denominator-norm"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_norm"),
                H("Ordinate separation controls every denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If abs(Im(z))>=10 then norm(s+1-z)>=10 for every real s. The low-frequency averaged kernel uses the imaginary-part bound without an inverse distance to Re(z)=1."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-denominator-ne"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_ne"),
                H("Nonvanishing denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same height condition makes s+1-z nonzero for every real s. SpectralAverage.window_kernel_integrable uses this fact in the continuity proof for the product kernel."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-resolvent-kernel-norm-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventKernel_norm_bound"),
                H("The pointwise positive resolvent majorant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Re(z)<=1, abs(Im(z))>=10, s>=0 and y>=0, the kernel norm is at most s*(1+s)*exp(-s*y)/10. SpectralAverage uses it to prove window product integrability and window_kernel_bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-resolvent-mode-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_bound"),
                H("Uniform modulus of a complete mode"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For y>0 under the same strip and height bounds, the full mode norm is at most W(y)/10. Together with W_antitone it gives the coefficient-summable window majorant used in spectral_average_bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("countableresolvent-resolvent-mode-continuous-on"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_continuousOn"),
                H("Mode continuity on a positive half-axis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Re(z)<1 and H>0, the mode is continuous on [H,infinity). The proof identifies it with the integrable W-weighted tail primitive. spectral_average_bound uses it for the actual measurability hypothesis of countable dominated convergence."))),
                DescribeRole.Lemma),
            Paragraph(Text("The existing CompleteCoefficientLaplace.complete_coefficient_laplace concerns the R-weight (1+x)/x^2 and numerator (1+t), so it is not the W-weight identity here. The generic real-moment supplier TwoScaleEndpointMoments.exponential_moment is reused instead of reproved; importing the instance-level LiCausalTrichotomy would violate this generic module’s import layer. ActualZeroLaplace and TrivialZeroLaplace provide actual occurrence and correction facts for a later application; this generic unit imports neither. The arithmetic relation to Q(exp(v)) and the original Robin5040 endpoint remain separate obligations.")))));
}
