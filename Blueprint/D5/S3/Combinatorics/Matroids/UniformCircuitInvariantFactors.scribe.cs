using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class UniformCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The invariant factors for a uniform core.",
        H("Uniform Circuit Invariant Factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-lifting-obstruction-invariant-factors"),
                DeclarationHandle.Create(Module + ".uniform_lifting_obstruction_invariant_factors"),
                H("The invariant factors for a uniform core"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a loopless uniform core have rank r + 2 on k + 2 ordered elements with r at most "
                    + "k. Expand each element to a nonempty class, with the order respecting the classes. The "
                    + "joint lifting quotient is a product of k choose r cyclic groups of order the gcd of "
                    + "the class sizes and k choose (r + 1) cyclic groups of order the total ground size. The "
                    + "alternating form reduction gives a pivot, then separates the coordinates according to "
                    + "whether their subset contains the direction of the remaining weight vector."))),
                DescribeRole.Theorem))));
}
