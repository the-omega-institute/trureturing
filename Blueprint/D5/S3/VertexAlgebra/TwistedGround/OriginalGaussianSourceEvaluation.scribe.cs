using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Evaluation of the Literal Signed Source",
        H("Finite Evaluation of the Literal Signed Source"),
        Blocks(
            Paragraph(Text("The finite Vandermonde identity is summed only after proving absolute double convergence. It evaluates the same-source sourceExternal, with 1-sourceExternal=A/F. No replacement source or covariance hypothesis is introduced.")),
            Describe.Lean(
                DescribeId.Create("external-parameter-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.external_parameter_bound"),
                H("external_parameter_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Bool label and every natural mode p, the complex norm of its signed half-integer binomial parameter is at most p+1."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourceamplitude"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude"),
                H("sourceAmplitude"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either signed label, natural p and complex x, A is the centralWeight series with coefficient (-1)^n choose(alpha-1/2,n). The full n=0 term is retained."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourceamplitude-hassum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude_hasSum"),
                H("sourceAmplitude_hasSum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and complex x with norm less than one, the normally summable shifted-central convolution, including s=0, sums to A."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourceexternal-evaluation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceExternal_evaluation"),
                H("sourceExternal_evaluation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and complex z with norm less than one, 1 minus the actual sourceExternal equals A at z squared divided by the original period at z squared."))), DescribeRole.Theorem))));
}
