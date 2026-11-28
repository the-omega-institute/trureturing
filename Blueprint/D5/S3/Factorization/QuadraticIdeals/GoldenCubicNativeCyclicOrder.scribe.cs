using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeCyclicOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclicOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical cyclic cubic carries an explicit integer order.",
        H("Exact denominator-two order of a Lucas block"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-cyclic-order-discriminant"),
                DeclarationHandle.Create(Module + "actual_order_discriminant"),
                H("The actual explicit order has exact trace discriminant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three marked vectors one, x, and half of x squared minus x span an integral subalgebra "
                    + "in the actual splitting field. Its trace discriminant is 81 times the block squared. Neither "
                    + "maximality nor exclusion of square-times-cube blocks is asserted."))),
                DescribeRole.Theorem))));
}
