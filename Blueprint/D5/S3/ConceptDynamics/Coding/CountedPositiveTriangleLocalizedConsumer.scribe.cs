using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedPositiveTriangleLocalizedConsumerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CountedPositiveTriangleLocalizedConsumer",
        H("The same signed integer gyration lift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countedpositivetrianglelocalizedconsumer-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue"),
                H("The same signed integer gyration lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The integer value at a compatible rectangular pair is exactly the accepted signedGyrationLift applied to the two matrices through Sum.elim. Its binomial-coefficient formula is integer valued on arbitrary signed tuples. It agrees on natural tuples with the accepted order-type lift; no new invariant is substituted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("countedpositivetrianglelocalizedconsumer-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three"),
                H("Transport the actual triangle to the integer lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The accepted equality between actual relative forward gyration and the order-type lift, followed by integer-cast compatibility, transports the proved numbered-path triangle modulo three. The same n,m,p and nonzero period divisible by three remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedpositivetrianglelocalizedconsumer-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle"),
                H("Include zero entries and empty intermediate dimensions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Entrywise toNat recovers a nonnegative integer matrix exactly. Matrix.map_mul transports all three products back to the natural counted triangle. The equality of the signed and natural binomial lifts then proves the integer triangle on nonnegative entries. Products may vanish when the intermediate dimension is zero, which is why this nonnegative statement is used instead of strict positivity of products."))),
                DescribeRole.Theorem))));
}
