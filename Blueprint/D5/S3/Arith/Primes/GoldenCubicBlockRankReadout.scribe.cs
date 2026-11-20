using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockRankReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact valuations of native cubic Lucas lags at every ordinary prime.",
        H("Rank readouts for all cubic Lucas lags"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-prime-fibonacci-rank-valuation-readout"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.valuation_eq_readout"),
                H("Rank hit, entry depth, and the index quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an odd prime, a positive Fibonacci index has depth zero unless its "
                    + "original entry rank divides the index. If it divides, the depth equals "
                    + "the entry depth plus the depth of the index divided by the rank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-all-odd-prime-rank-lag"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_lag"),
                H("Exact native block lag depth without a witness hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct levels, the lag depth is the sum of the two Fibonacci rank "
                    + "readouts at the sum and difference indices, with an extra one at five. "
                    + "This holds also for primes which never divide any Lucas block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-all-odd-prime-rank-collision"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_collision"),
                H("Exact residue collision at every odd-prime precision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two readings coincide modulo the given prime power exactly when its "
                    + "exponent fits within their computed joint rank depth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-all-prime-lag"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_all_prime_lag"),
                H("All ordinary primes, including the first dyadic step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The odd-prime readouts combine with the dyadic clock to classify every "
                    + "prime. At two, the level-zero block and every later block differ already "
                    + "modulo two, and two positive levels obey the exact dyadic lag law."))),
                DescribeRole.Theorem))));
}
