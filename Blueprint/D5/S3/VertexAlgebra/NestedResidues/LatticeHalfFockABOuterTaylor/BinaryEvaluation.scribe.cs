using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor;

internal sealed class BinaryEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Laurent evaluation consumed by the actual middle equality",
        H("BinaryEvaluation"),
        Blocks(
            Paragraph(Text("Both remaining Hahn orders are expanded from the same complete binary rational field. The numerator has arbitrary signed exponents. The complete forward-minus-signed-reverse jump is evaluated before the fractional finite sum. The contextual coefficient is a direct specialization of ContextualKernelExtraction.contextual_kernel_coeff at prefix=suffix=0.")),
            Paragraph(Text("binary_fractional_taylor is a consumed bind-only helper. Its actual consumer is the private actual_ab_binary_taylor in the parent, which applies it after padding genuine complete-field locality to max(B(j),H(j)). This child is not a standalone Laurent theorem publication or a replacement endpoint for the original equality.")),
            Describe.Lean(
                DescribeId.Create("binary-fractional-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/BinaryEvaluation.binary_fractional_taylor"),
                H("binary_fractional_taylor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained."))),
                DescribeRole.Theorem))));
}
