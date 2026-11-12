using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualBoundaryPriceLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual boundary prices from legal prime exchanges on full predecessor records.",
        H("Conditional BHP boundary-price localization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-price-variation"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.price_variation"),
                H("Variation of the real layer price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For j>=1 and a>=2, the difference between beta(j,x) and beta(j,y) for x,y>=a is at most priceLip(j,a)*abs(y-x). The logarithmic derivative estimate is uniform on the whole ray, including its lower endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-uniform-coarse-geometry"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_coarse_geometry"),
                H("Separation on every original record"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each fixed j>=2 a single positive threshold precedes every m>=2 and every original mu>0 with the full strict predecessor record. With P=largestPrime(m) and Q=layerPrime(m,j), P>=4, Q>=4, Q<=P/8, the second layer is strictly below P/2, and log(Q/2)>=log(P)/(4*j). No optimizer at a replacement price is substituted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-counted-higher-pools"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.counted_higher_pools"),
                H("Exact prime cardinalities on both sides"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied two-sided short-interval count and capacity K+1 give two finite sets of exactly K distinct actual primes near a natural endpoint N. The lower set retains the closed upper endpoint; the upper set excludes N. The extra unit pays for deleting a possible prime endpoint. This result uses the count supplier directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-uniform-counted-first-pools"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_counted_first_pools"),
                H("Uniform pools around the first prime"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed j>=2 and positive count constants C,c, one threshold gives lower and strict upper prime pools of cardinality ceil(P^(19/(40*j))) around every sufficiently large natural P. Their radius C*P^(21/40) is nonnegative and at most P/2. The complete count hypothesis quantifies over every real x beyond its threshold."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-uniform-higher-geometry"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.uniform_higher_geometry"),
                H("Higher-layer capacity and legal valuation bands"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed j>=2 and positive C,c, one threshold precedes all full records and original positive prices. The higher-layer root Q supplies the requested cardinality plus the endpoint allowance in radius C*Q^(21/40); the neighboring layers lie outside the comparison bands, and P<=Q^j. The argument combines the existing record ratio and scale limits on the same integer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-first-beta-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.first_beta_lower"),
                H("Lower bound for the first price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real P>=2, 1/(P*log(P))<=2*beta(1,P). The elementary logarithm lower bound controls the actual first marginal price, rather than replacing it by an asymptotic reference price."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-boundary-price-lip-half-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.priceLip_half_bound"),
                H("A common logarithmic scale for the variation bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Q>=4, P>1 and D>0 with log(P)/D<=log(Q/2), priceLip(j,Q/2) is bounded by ((j+2)*2^(j+1)*D)/(Q^(j+1)*log(P)). This translates the local price variation to the first-prime logarithmic scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-bhp-boundary-price-localization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization.bhp_boundary_price_localization"),
                H("Conditional actual boundary-price localization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the literal BHPMaximumGap and the independent two-sided BHPShortIntervalCount, both at exponent 21/40. For every fixed j>=2 there are positive C,T before all m>=2 and all original mu>0. If every positive n<m has strictly smaller goldenResourceObjective(mu,n), and P=largestPrime(m)>=T, then abs(beta(j,layerPrime(m,j))-beta(1,P))<=C*beta(1,P)*P^(-19/(40*j)). Actual finite exchanges use the original valuations, including valuation excess. The count route does not infer the count hypothesis from the maximum-gap hypothesis. The statement is conditional: neither analytic supplier is proved here, and it establishes neither full bank payment nor Robin or RH."))),
                DescribeRole.Theorem))));
}
