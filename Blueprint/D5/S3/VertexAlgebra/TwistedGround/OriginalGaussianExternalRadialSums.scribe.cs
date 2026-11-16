using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;
internal sealed class OriginalGaussianExternalRadialSumsDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
  "Radial Differentiation of the Original T Generator", H("Radial Differentiation of the Original T Generator"), Blocks(
   Paragraph(Text("The literal square-resolvent mode series is differentiated on the radial square-root disk by a local complex normal-convergence argument.")),
   Describe.Lean(DescribeId.Create("kernel-mode-radial-derivative"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative"), H("kernelMode_radial_derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every signed pair and 0<r<1 with the two mode radii inside the convergence disk, the real radial derivative of the full literal T generator is the normally convergent sum of the radial derivatives of its original mode coefficients. The proof uses the actual external vectors, square resolvent, and square-root chain rule."))), DescribeRole.Theorem))));
}
