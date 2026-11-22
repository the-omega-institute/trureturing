using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SunflowerCircuitWeightBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pivot and a disjoint family of coordinate sets admit a shared weight basis.",
        H("Weight Coordinates for Disjoint Petals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-sunflower-weight-basis"),
                DeclarationHandle.Create(Module + ".exists_sunflower_weight_basis"),
                H("Weight Coordinates for Disjoint Petals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a finite coordinate set with positive integer weights and pairwise disjoint "
                    + "petals, each of size at least two and each avoiding the pivot. Partition the "
                    + "indices by petal membership and by equality to the pivot. An integral change "
                    + "of basis concentrates the weights on one index per block. The change and its "
                    + "inverse preserve each petal, and the inverse change sends the pivot vector to "
                    + "a coordinate vector supported at the pivot. Each petal meets the zero-weight "
                    + "set away from the pivot, so the intersections for distinct petals differ."))),
                DescribeRole.Theorem))));
}
