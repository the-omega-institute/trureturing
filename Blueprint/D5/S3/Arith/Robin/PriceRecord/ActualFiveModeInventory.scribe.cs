using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualFiveModeInventoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual signed prime inventories and predecessor.",
        H("Actual signed prime inventories and predecessor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualfivemodeinventory-actual-high-inventory"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory.actual_high_inventory"),
                H("Actual higher-layer donors and recipients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under both independent BHP suppliers, each fixed j>=2 has positive A,W,T before every original positive-price full record. Two disjoint actual prime sets have exactly comparisonCount(j,P) elements, all above 2. The lower primes have original valuation j and the upper primes original valuation j-1. The full radius, layer-power comparison and relative boundary-price error remain explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodeinventory-actual-first-inventory"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory.actual_first_inventory"),
                H("First-layer inventory at count index sixteen"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The independent short-interval count supplier gives positive W,T uniformly over original positive-price full records. The disjoint lower and upper first-prime pools each have comparisonCount(16,P) elements, all above 2; the lower valuations are exactly 1 and upper valuations exactly 0. The complete radius is at most P/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodeinventory-actual-finite-predecessor"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory.actual_finite_predecessor"),
                H("Exact same-record finite predecessor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m>=2 at an original mu>0 full record, disjoint finite donor and recipient prime sets above 2, donors dividing m, and positive log(2)+logMass(D)-logMass(U), there is a positive n<m with exactly that logarithmic deficit. Its 2-adic valuation is lower by exactly one. At arbitrary real lambda the objective difference is exactly topGain(lambda,m)+auxiliaryGain(lambda,m,D,U), and the original record gives the strict upper bound for topGain displayed in Lean. Both fee signs and the highest occupied 2-layer are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodeinventory-uniform-actual-clock"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory.uniform_actual_clock"),
                H("Uniform clock on the original integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One positive threshold precedes every m>=2 and original mu>0 full record. Above it log(P)>=1, log(log(m))>0, and log(P)/2<=log(log(m))<=2*log(P). This is a same-integer estimate; it introduces no later critical-chain price."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodeinventory-eventual-mass-error-absorption"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory.eventual_mass_error_absorption"),
                H("Fourth mesh absorbs the summed error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonnegative real K, eventually mesh4(X)>0 and K*log(X)*X^(-19/640)<=mesh4(X)/2. The original fourth-order mesh remains the comparison scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodeinventory-pointwise-boundary-estimates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeInventory.pointwise_boundary_estimates"),
                H("Pointwise logarithmic and complete marginal-fee errors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For j>=1, R,Q>=4, Q<=R<=Q^j, nonnegative W,A,H, the explicit logarithmic scale, radius, relative price and root-error hypotheses give both displayed estimates for every actual prime in the closed interval around Q. One estimate controls its logarithmic mass against root/j; the other controls the full marginal fee against beta(1,R), with the complete j-dependent constant."))),
                DescribeRole.Theorem))));
}
