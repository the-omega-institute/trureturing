using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitOmittedFaceProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitOmittedFaceProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent coordinate restrictions in the pivoted kernel.",
        H("Product Identity for Two Face Equations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pivoted-face-product"),
                DeclarationHandle.Create(Module + ".pivoted_face_product"),
                H("Independent coordinate restrictions in the pivoted kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Concentrate the weights within the blocks determined by the two faces and the pivot. Both face coefficients retain their vanishing conditions. The two faces intersect the zero-weight indices differently, so the product of the unrestricted and doubly restricted modules is equivalent to the product of the two single restrictions."))),
                DescribeRole.Theorem))));
}
