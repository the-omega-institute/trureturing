using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class FourFieldMiddleInverseKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("FourFieldMiddleInverseKernel", H("Outer native inverse kernel"), Blocks(Paragraph(Text("The three native binomial inverses expand U+STU, U and TU. Exact finite convolutions reindex the first power Q as H+M, deriving the four outer indices. The N3 balanced kernel is reused by the coefficient theorem.")))));
}
