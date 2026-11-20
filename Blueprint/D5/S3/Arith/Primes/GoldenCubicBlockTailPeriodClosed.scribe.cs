using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockTailPeriodClosedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least congruence period of a later Lucas-block stream separates its Lucas depth from the base-three Fermat depth.",
        H("Closed least periods of cubic Lucas block tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-order-nine-prime-power"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.orderOf_nine_prime_power"),
                H("The base-three threshold for lifting the order of nine"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an odd prime other than three, let t be the order of nine modulo p "
                    + "and e the valuation of three to the power p minus one, minus one. "
                    + "At positive precision r the order is t times p to the power max(0,r-e)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-native-least-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_least"),
                H("Least positive period at every precision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime divisor of an earlier Lucas block, let h be its valuation in "
                    + "that block. Later blocks are constant modulo p^a through a=2h. "
                    + "Above that precision the least period is t times p to the power "
                    + "max(0,a-2h-e), and all return periods are multiples of it. "
                    + "This does not determine which blocks have an exponent-one factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-period-profile-cutoffs"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.cubicTailPeriod_profile_cutoffs"),
                H("Recover both depths from the period profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The period one plateau ends exactly at 2h and the first nontrivial "
                    + "period plateau ends at 2h+e. The separation of the two depths can "
                    + "therefore be read back from the stream itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-native-least-period-nineteen"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_nineteen"),
                H("All precisions for the first block prime 19"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For p=19 and the first block, the computed period is one through "
                    + "precision two and 9 times 19 to the power a-3 thereafter."))),
                DescribeRole.Theorem))));
}
