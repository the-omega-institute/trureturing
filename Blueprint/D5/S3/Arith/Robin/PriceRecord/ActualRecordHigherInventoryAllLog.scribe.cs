using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordHigherInventoryAllLogDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherInventoryAllLog";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the original strict record clock, the full higher inventory differs from the reference "
        + "inventory by less than its square root scale divided by any fixed power of its logarithm.",
        H("Higher inventory convergence on original strict records"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-record-all-real-log-higher-inventory"),
            DeclarationHandle.Create(Module + ".actual_record_all_real_log_higher_inventory"),
            H("One threshold for all sufficiently late original strict records"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every real a and every epsilon > 0 there is X0 > 1 such that, for every "
                    + "integer m >= 2 and every real mu > 0 at which the objective of m is strictly "
                    + "larger than the objective of each positive predecessor, X = log m >= X0 "
                    + "implies 0 <= (log X)^a times the weighted mismatch divided by sqrt(X) "
                    + "and this quotient is strictly below epsilon.")),
                Paragraph(Text(
                    "At X = log m, sum log p over the symmetric difference of higher prime-power "
                    + "coordinates in m and in the strict reference optimizer at price 1/(X log X). "
                    + "The original positive price of m enters through its strict predecessor comparisons.")),
                Paragraph(Text(
                    "Apply finite inventory duality on each coordinate before summing, so missing and "
                    + "excess coordinates do not cancel in the bound. Balance the resulting loss term with "
                    + "the higher mass response between two nearby reference prices. This controls the "
                    + "weighted mismatch with the literal higher-layer loss and an additive log-squared term.")),
                Paragraph(Text(
                    "For a real exponent a, apply the uniform higher loss bound at exponents 2a+2 "
                    + "and a+1. These control the square-root and linear terms after normalization. "
                    + "The remaining term tends to zero because a fixed real power of log X grows "
                    + "more slowly than the square root of X."))),
            DescribeRole.Theorem))));
}
