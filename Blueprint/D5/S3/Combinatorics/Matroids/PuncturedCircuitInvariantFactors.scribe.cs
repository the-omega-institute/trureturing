using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PuncturedCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic factors with one omitted uniform basis.",
        H("Punctured Circuit Invariant Factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("punctured-lifting-obstruction-invariant-factors"),
                DeclarationHandle.Create(Module + ".punctured_lifting_obstruction_invariant_factors"),
                H("The cyclic factors after one basis is omitted"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the ordered core on k elements have rank r with 2 at most r and r strictly less "
                    + "than k. Its bases are all r-subsets except one H. In a parallel expansion whose order "
                    + "respects the classes, put n equal to the total size and g equal to the gcd of all "
                    + "class sizes. The joint lifting quotient has binomial(k-2,r-2) minus one factors of "
                    + "order g, binomial(k-2,r-1) minus one factors of order n, and one factor of order the "
                    + "gcd of n and the sizes outside H."))),
                DescribeRole.Theorem))));
}
