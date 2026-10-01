using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaBasicSumFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every permutation has a unique factorization into nonempty sum-indecomposable permutations.",
        H("Unique Direct-Sum Factorization"),
        Blocks(
            Node("fundamental-bijection-thetabasicsumfactors-sumfactors", "The sum of a sequence of factors", "sumFactors",
                "The sum of an empty sequence of factors is empty; otherwise concatenate the first factor with the sum of the remaining factors after increasing every remaining value by the length of the first factor.", DescribeRole.Definition),
            Node("fundamental-bijection-thetabasicsumfactors-exists-sum-factorization", "Existence of indecomposable factors", "exists_sum_factorization",
                "Every permutation can be expressed as the sum of a sequence of nonempty permutations, each of which has no proper nonempty direct-sum cut.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetabasicsumfactors-sum-factorization-unique", "Uniqueness of indecomposable factors", "sum_factorization_unique",
                "Two sequences of nonempty sum-indecomposable permutations with the same direct sum are equal.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
