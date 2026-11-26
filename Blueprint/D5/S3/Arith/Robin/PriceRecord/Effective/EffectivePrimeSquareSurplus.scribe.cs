using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.Effective;

internal sealed class EffectivePrimeSquareSurplusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact prime-square band reserve from the complete actual Robin ledger.",
        H("Exact prime-square surplus in the actual Robin ledger"),
        Blocks(
            Paragraph(Text("For a real cutoff z and a positive integer n whose prime support is exactly the primes at most z, the complete signed prime-power ledger is retained. Every occupied prime p with p^2>2z contributes a strict explicit weight (p-2)/(2(p-1)p^2), including the whole shifted Euler tail and every actual valuation.")),
            Paragraph(Text("The finite band is the filtered prime set p<=floor(z) and 2z<p^2. The normalized band multiplies its exact rational weights by sqrt(z) log z. The reserve needed for the weighted zero term and the log-log curvature is stated with the exact constants 1/20, 2 and 1/8.")),
            Describe.Lean(DescribeId.Create("prime-band-weight"), DeclarationHandle.Create(Prefix + "primeBandWeight"), H("Prime-band weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact weight assigned to a prime p is (p-2)/(2(p-1)p^2)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-band"), DeclarationHandle.Create(Prefix + "primeBand"), H("Actual prime band"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The band contains exactly the primes p at most floor(z) with 2z<p^2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arithmetic-surplus"), DeclarationHandle.Create(Prefix + "arithmeticSurplus"), H("Complete arithmetic surplus"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This is the complete tail plus the exact log(n)-psi(z) inventory divided by z log z, less the full prime-power residual."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalization"), DeclarationHandle.Create(Prefix + "D"), H("Square-root logarithmic normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The normalization is sqrt(z) log z."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-band"), DeclarationHandle.Create(Prefix + "normalizedPrimeBand"), H("Normalized prime band"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The normalized band is D(z) times the finite sum of prime-band weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("needed-reserve"), DeclarationHandle.Create(Prefix + "neededReserve"), H("Required analytic reserve"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The required reserve is (1/20)(1+1/log z)+2/sqrt z+(1+1/log z)/(8z sqrt z)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-surplus"), DeclarationHandle.Create(Prefix + "prime_contribution_sqrt_two"), H("Strict local prime-square surplus"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For z>=4, p<=z prime, p^2>2z and positive actual valuation, the exact prime-band weight is strictly below the complete local prime contribution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ledger-band"), DeclarationHandle.Create(Prefix + "prime_band_le_full_surplus"), H("Band reserve below the full ledger"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Summing the strict local inequalities over the actual band and retaining nonnegative contributions from every other supported prime gives the band sum at most the complete arithmetic surplus."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("effective-margin"), DeclarationHandle.Create(Prefix + "robin_margin_of_effective_band"), H("Effective Robin margin reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A finite positive margin through log height 101, an exact prime-band reserve for every cutoff z>=100, and the weighted-tail lower bound together imply a positive original Robin log margin for every n>5040."))), DescribeRole.Theorem)
        )));
}
