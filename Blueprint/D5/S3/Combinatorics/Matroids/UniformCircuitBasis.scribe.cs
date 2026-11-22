using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class UniformCircuitBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/UniformCircuitBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The gcd coordinate for a positive weight vector.",
        H("Uniform Circuit Basis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weight-vector-in-basis"),
                DeclarationHandle.Create(Module + ".weight_vector_in_basis"),
                H("The gcd coordinate for a positive weight vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite index set, a positive weight vector is its gcd times a vector in an "
                    + "integral basis. Dualize the unimodular change of coordinates that reduces the weighted "
                    + "scalar sum to a single coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-adapted-weight-basis"),
                DeclarationHandle.Create(Module + ".exists_adapted_weight_basis"),
                H("A basis adapted to both operations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive integer weight vector on k + 2 coordinates, there is an integral basis "
                    + "whose first vector sums to one and in which the weight vector is the total weight "
                    + "times that first vector plus the gcd of the remaining original weights times the "
                    + "second vector."))),
                DescribeRole.Theorem))));
}
