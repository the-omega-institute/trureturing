using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class StrictDivisorChainCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Divisor Chain Counts.",
        H("Strict Divisor Chain Counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strictdivisorchaincount-strict-divisor-chain-count"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.strict_divisor_chain_count"),
                H("The signed binomial counting formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural endpoint n greater than one and for every length 1 ≤ k ≤ Ω(n), "
                    + "where Ω(n) counts prime factors with multiplicity, "
                    + "the number of strict divisor chains from one to n is the sum, over j from zero "
                    + "through k, of the weak counting function multiplied by binomial k choose j "
                    + "and the sign negative one to the power k minus j. The weak counting function "
                    + "is zero at length zero and otherwise is the product, over prime divisors p of n, "
                    + "of binomial a_p plus j minus one choose a_p, where a_p is the exponent of p in n. "
                    + "Successive quotients identify weak chains with positive factor tuples and strict "
                    + "chains with positive factor tuples whose entries are all different from one. Prime "
                    + "factorization identifies positive factor tuples with exponent compositions. Deleting "
                    + "prescribed unit factors gives the intersections used in finite inclusion-exclusion."))),
                DescribeRole.Theorem))));
}
