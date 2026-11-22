using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class TwoOmittedCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/TwoOmittedCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint lifting obstruction for a core with two separated omissions.",
        H("Cyclic Factors with Two Omitted Uniform Bases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-omitted-lifting-obstruction-invariant-factors"),
                DeclarationHandle.Create(Module + ".two_omitted_lifting_obstruction_invariant_factors"),
                H("The two separate cyclic factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a uniform core of rank at least three and corank at least two. Omit two bases "
                    + "whose intersection is at most two below the rank. In a block-ordered parallel expansion, "
                    + "write n for the total size and g for the gcd of the class sizes. Starting from the uniform "
                    + "decomposition, decrease the multiplicities of the factors of orders g and n by two each. "
                    + "For each omitted basis, add a cyclic factor whose order is the gcd of n and the class "
                    + "sizes outside that basis. The two exceptions may have incomparable orders. The residue "
                    + "product identity and cancellation of the uniform factors give the stated decomposition."))),
                DescribeRole.Theorem))));
}
