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
                    + "respects the original fibers in both directions of the change of coordinates. "
                    + "The weight is zero on every other basis coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tuple-vanishing-iff-of-supported-change"),
                DeclarationHandle.Create(Module + ".tuple_vanishing_iff_of_supported_change"),
                H("Vanishing of a face coefficient under a supported change of basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If both directions of a change of coordinates preserve a given subset, the "
                    + "old and new basis vectors on that subset span the same integral submodule. "
                    + "An alternating form of the corresponding degree vanishes on the old basis "
                    + "tuple exactly when it vanishes on the new one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-basis-separating-faces"),
                DeclarationHandle.Create(Module + ".exists_basis_separating_faces"),
                H("Separating the zero-weight intersections of two faces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Partition the indices by membership in the two faces. Each block has at "
                    + "most one weighted direction after an integral change of basis. If the "
                    + "first face has two indices outside the second, one of them has zero "
                    + "weight, so the two intersections with the zero-weight set differ. "
                    + "The changed coordinates preserve the spans of both faces."))),
                DescribeRole.Theorem))));
}
