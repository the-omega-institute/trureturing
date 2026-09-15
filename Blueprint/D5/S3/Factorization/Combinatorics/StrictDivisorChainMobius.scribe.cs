using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class StrictDivisorChainMobiusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Divisor Chains and the Möbius Function.",
        H("Strict Divisor Chains and the Möbius Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strictdivisorchainmobius-chain-alternating-sum-eq-moebius"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/StrictDivisorChainMobius.chain_alternating_sum_eq_moebius"),
                H("The alternating chain formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive integer n, the alternating sum of the numbers of strict "
                    + "divisor chains from one to n equals the Möbius function at n. The sum includes "
                    + "lengths from zero through Ω(n), the number of prime factors with multiplicity. "
                    + "Removing the last step partitions nonempty chains by their penultimate proper "
                    + "divisor. Strict chains have length at most Ω(n), so this partition gives the "
                    + "divisor recursion for the alternating sum. At n = 1 the unique empty chain "
                    + "contributes one. These initial and recursive values determine the Möbius function."))),
                DescribeRole.Theorem))));
}
