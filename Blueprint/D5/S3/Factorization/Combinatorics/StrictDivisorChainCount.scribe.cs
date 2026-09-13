using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class StrictDivisorChainCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Divisor Chains.",
        H("Strict Divisor Chains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strictdivisorchaincount-weak-chain-count"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.weak_chain_count"),
                H("Counting weak divisor chains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every endpoint greater than one and every natural length, the number of "
                    + "weak divisor chains is the product of the prime-exponent composition counts, "
                    + "with zero chains at length zero. Successive quotients identify chains with "
                    + "positive factor tuples, and factorization identifies these tuples with "
                    + "independent weak compositions of the prime exponents."))),
                DescribeRole.Theorem))));
}
