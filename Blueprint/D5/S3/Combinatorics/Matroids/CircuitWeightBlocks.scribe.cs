using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitWeightBlocksDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitWeightBlocks";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral changes of coordinates on the fibers of a partition.",
        H("Concentrating Circuit Weights within Each Block"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-weight-basis-by-fiber"),
                DeclarationHandle.Create(Module + ".exists_weight_basis_by_fiber"),
                H("One weighted direction in each fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A partition of the indices gives a product of the corresponding integral "
                    + "coordinate modules. Choose an integral basis in each fiber so its weight "
                    + "vector is the fiber gcd times a single basis vector. The combined basis "
                    + "is supported within the original fibers and the weight is zero on every "
                    + "other basis coordinate."))),
                DescribeRole.Theorem))));
}
