using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualBoundaryPriceGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual boundary-price exchange geometry.",
        H("Actual boundary-price exchange geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualboundarypricegeometry-pricelip-nonneg"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.priceLip_nonneg"),
                H("Nonnegative local price bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural j and real a>=2, priceLip(j,a) is nonnegative. This sign is used in the normalized actual boundary-price cost."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-price-variation"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.price_variation"),
                H("Variation of the real layer price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For j>=1 and a>=2, the difference between beta(j,x) and beta(j,y) for x,y>=a is at most priceLip(j,a)*abs(y-x). The logarithmic derivative estimate is uniform on the whole ray, including its lower endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-uniform-coarse-geometry"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.uniform_coarse_geometry"),
                H("Separation on every original record"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each fixed j>=2 a single positive threshold precedes every m>=2 and every original mu>0 with the full strict predecessor record. With P=largestPrime(m) and Q=layerPrime(m,j), P>=4, Q>=4, Q<=P/8, the second layer is strictly below P/2, and log(Q/2)>=log(P)/(4*j). No optimizer at a replacement price is substituted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricegeometry-actual-boundary-price-from-pools"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.actual_boundary_price_from_pools"),
                H("Price obstruction from four actual prime pools"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix j>=2. One positive threshold precedes all original positive-price full records. With P=largestPrime(m), Q=layerPrime(m,j), K=ceil(P^(19/(40*j))), four actual prime sets of cardinality K in the stated lower and upper windows give abs(beta(j,Q)-beta(1,P))<=priceLip(j,Q/2)*w+priceLip(1,P/2)*v+(8*j/K)*(beta(1,P)+priceLip(1,P/2)*v). The windows have independent widths w<=Q/2 and v<=P/2, and the higher-layer bands retain their neighboring-layer constraints. The strict predecessor exchanges use original valuations and bounded rounding costs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualboundarypricelocalization-counted-higher-pools"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry.counted_higher_pools"),
                H("Exact prime cardinalities on both sides"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied two-sided short-interval count and capacity K+1 give two finite sets of exactly K distinct actual primes near a natural endpoint N. The lower set retains the closed upper endpoint; the upper set excludes N. The extra unit pays for deleting a possible prime endpoint. This result uses the count supplier directly."))),
                DescribeRole.Theorem))));
}
