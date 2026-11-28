using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicClockCofinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eventual native Lucas clocks observe every positive time modulus.",
        H("Cofinal native Lucas clocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-clock-period-monotone"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_dvd_of_modulus_dvd"),
                H("Divisibility of observation moduli implies divisibility of periods"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A late return at the finer observation modulus gives a late return "
                    + "at the coarser modulus, so its least positive period is a multiple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-clock-ternary-outside-three"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicClockCofinality.ternary_time_observed_at_other_prime"),
                H("Every ternary time digit can be observed at a prime other than three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a cyclotomic prime where the order of nine is the requested "
                    + "power of three. A sufficiently fine signed Lucas clock at that same "
                    + "prime retains the entire ternary time digit window."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-clock-cofinal"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_cofinal"),
                H("Every time modulus divides a native observation period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Own-prime growth and cross-prime ternary growth supply every prime "
                    + "power, and a common multiple of the observation moduli combines "
                    + "these time requirements into one finite clock."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-clock-three-isolation"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_block_isolated_at_three"),
                H("Three separates every actual reading yet loses time in the limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Three-adic precision indexed by one actual level separates that level "
                    + "from all the other actual levels. Conversely, each fixed precision "
                    + "eventually reads one."))),
                DescribeRole.Theorem))));
}
