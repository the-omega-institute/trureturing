using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldBalancedInverseKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite diagonal and coupled coefficients", H("Finite diagonal and coupled coefficients"), Blocks(
            Describe.Lean(DescribeId.Create("threefieldbalancedinversekernel-balanced-inverse-coeff"),
                DeclarationHandle.Create(Prefix + "balanced_inverse_coeff"),
                H("Finite diagonal and coupled coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal binomial kernel consumes l degrees in both native variables. The coupled kernel consumes r and r+j degrees. Their product therefore consumes r+l and r+j+l degrees, with the sign (-1)^j."))), DescribeRole.Theorem))));
}
