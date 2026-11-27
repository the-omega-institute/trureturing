using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.AllSupport;

internal sealed class AllSupportRobinPrimeBlockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite weighted Chebyshev integral lower bounds the actual Robin prime cost.",
        H("A finite lower bound for the Robin prime cost"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-prime-cost-block"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/AllSupport/PrimeBlock.theta_weight_two_block_le_prime_cost"),
                H("Chebyshev theta with the index-two Robin weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For h at least 8, the prime cost is at least the integral of theta(t) "
                    + "against the index-two Robin weight over (sqrt(2h), h/2]. "
                    + "The reciprocal-square sum on this interval and the theta prefix at "
                    + "sqrt(2h) jointly bound the integral by Abel summation. "
                    + "The lower endpoint enters through the prefix and the upper endpoint "
                    + "enters through the reciprocal-square sum."))),
                DescribeRole.Theorem))));
}
