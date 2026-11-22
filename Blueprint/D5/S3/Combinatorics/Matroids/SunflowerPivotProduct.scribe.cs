using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SunflowerPivotProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SunflowerPivotProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A new petal coefficient is independent of coefficients on disjoint petals "
        + "of size at least two avoiding the pivot.",
        H("The Product of Pivoted Form Modules"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sunflower-pivot-product"),
                DeclarationHandle.Create(Module + ".sunflower_pivot_product"),
                H("The Product of Pivoted Form Modules"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use alternating forms in an integral basis indexed by a finite ordered set. "
                    + "Fix a pivot, a vector with positive integer weights, and an integer n. "
                    + "In the submodule killed by n and by insertion of the pivot and weighted "
                    + "vectors, impose coefficient conditions at disjoint petals of the form degree, "
                    + "which is at least two. Every petal avoids the pivot. The adapted basis "
                    + "preserves the pivot line and each coefficient kernel. Projection to the new "
                    + "petal sector commutes with both insertions and preserves n-torsion. "
                    + "Sector exchange identifies the unrestricted module times the jointly "
                    + "restricted module with the product for the prior and new conditions separately."))),
                DescribeRole.Theorem))));
}
