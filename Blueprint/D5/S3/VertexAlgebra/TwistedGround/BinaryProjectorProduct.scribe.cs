using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class BinaryProjectorProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary character projector equals the product of commuting half-sum involutions.",
        H("The Hyperbolic Projector Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binaryprojectorproduct"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct.product_equals_plus"),
                H("The Hyperbolic Projector Product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The operator (I+F_i)/2 is attached to each coordinate unit. The factors commute by the binary subgroup law. In the commutative additive group algebra, expanding the product corresponds to choosing either zero or one in each binary coordinate.")),
                    Paragraph(Text("The product of coordinate-unit group elements is the original binary half itself. The universal algebra homomorphism into the given endomorphism algebra sends each group element to its actual F-action. Thus the finite product is exactly 2^(-n) times the sum of all F-actions. This identity is used for the original chosen native projector."))),
                DescribeRole.Theorem))));
}
