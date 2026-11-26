using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.Effective;

internal sealed class EffectivePrimeBandCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational prime-band certificates cover every real cutoff from 100 through 10000.",
        H("Finite exact prime-band certificates"),
        Blocks(
            Paragraph(Text("Five closed intervals cover 100<=z<=10000. Each interval uses a finite roster of actual primes p<=L with p^2>2U, a certified square-root lower bound r, and a rational lower bound ell for log L.")),
            Paragraph(Text("The certificate keeps both real endpoints and the upper prime-band endpoint. All comparisons use exact rational logarithm enclosures and the native prime-band weight from EffectivePrimeSquareSurplus.")),
            Describe.Lean(DescribeId.Create("interval-certificate"), DeclarationHandle.Create(Prefix + "interval_certificate"), H("Single interval certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A roster satisfying the exact prime, endpoint, root and logarithm hypotheses proves neededReserve z < normalizedPrimeBand z throughout the closed interval [L,U]."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-band"), DeclarationHandle.Create(Prefix + "normalized_prime_band_finite"), H("Finite cutoff coverage"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The five literal rosters certify neededReserve z < normalizedPrimeBand z for every real z with 100<=z<=10000."))), DescribeRole.Theorem)
        )));
}
