using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldInnerInverseKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coupled inner inverse kernel", H("The coupled inner inverse kernel"), Blocks(
            Describe.Lean(DescribeId.Create("inner-inverse-coeff"),
                DeclarationHandle.Create(Prefix + "inner_inverse_coeff"),
                H("The varying inverse order 2k+r"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middle binomial kernel and the second difference kernel combine by the integer-binomial shift identity and the binomial-series group law. Their coefficient at S^r T^s is (-1)^s binom(-k,r) binom(-(2k+r),s-r) when r <= s. Convolution with (1+S)^(-H) gives the stated finite l sum. Every spectator degree and zero exponent is included. The binomial-series suppliers retain Scott Carnahan attribution."))), DescribeRole.Theorem))));
}
