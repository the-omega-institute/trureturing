using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CommonBandSharpnessTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport of sparse cusp energy to the original price-weighted response.",
        H("Sparse cusp transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profile-cross"),
                DeclarationHandle.Create(Prefix + "profileCross"),
                H("Price-weighted profile cross energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The profile cross energy integrates the product of the actual constant-profile responses at exponents a and b against dx/x over [X,2X]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("isolated-spike-normalized-response"),
                DeclarationHandle.Create(Prefix + "profileResponse_spike_normalized"),
                H("Normalized response of an isolated spike"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an admissible spike and every x between its center X and 2X, with 0 <= theta <= b <= 1, the response divided by sqrt(x) equals A/x^theta times the unit integral of the cusp increment multiplied by the original price ratio. Isolation holds for every forward displacement up to 2X^b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixed-profile-cross-integrable"),
                DeclarationHandle.Create(Prefix + "profileCross_integrable"),
                H("Integrability of mixed responses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two locally bounded measurable error functions and arbitrary exponents, the product of their constant-profile responses divided by x is integrable on each compact interval above three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spike-price-removal-error"),
                DeclarationHandle.Create(Prefix + "profileCross_spike_price_error"),
                H("Price removal for a sparse cusp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If X is an admissible spike center above four and 8X^b/X <= 1, the difference between its actual cross energy and A^2 times the moving cusp energy has absolute value at most 16X^b/X times that unweighted moving energy. Both price ratios are nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spike-cross-energy-estimate"),
                DeclarationHandle.Create(Prefix + "profileCross_spike_estimate"),
                H("Transported cusp energy estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<a<b<1 and an admissible starting index, there is C>0 such that eventually at the centers X, writing h=X^a, k=X^b and L=log(k/h), the actual cross energy differs from A^2 X^(-a-b) hL^2/4 by at most C A^2 X^(-a-b) times hL+(k/X)hL^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spike-cross-energy-asymptotic"),
                DeclarationHandle.Create(Prefix + "profileCross_spike_asymptotic"),
                H("Cross energy at the spike centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<a<b<1 and an admissible starting index, the actual constant-profile cross energy divided by X^(1-b)log(X)^3/log(log(X)) tends along the spike centers to (b-a)^2/4. The product normalization is exactly x^(-a-b)."))),
                DescribeRole.Theorem))));
}
