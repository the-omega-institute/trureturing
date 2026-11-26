using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentStarProductsDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9LaurentStarProducts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laurent transport fixes the two transverse star centers.",
        H("Products of transverse stars"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-transverse-star-product"),
                DeclarationHandle.Create(Owner + "actual_transverse_star_product"),
                H("Laurent transport fixes the two transverse star centers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two transverse coordinate blocks each have three-leaf star fibers. Two distinct centers in one parity class have common leaf positions with opposite Laurent increments. Transport between fibers forces those increments to agree, giving one product of two stars."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentTransverseFibers"))]));
}
