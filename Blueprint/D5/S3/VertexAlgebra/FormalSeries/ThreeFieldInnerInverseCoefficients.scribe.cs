using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldInnerInverseCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite numerator reconstruction of the inner inverse", H("Finite numerator reconstruction of the inner inverse"), Blocks(
            Describe.Lean(DescribeId.Create("raw-inner-coefficients"),
                DeclarationHandle.Create(Prefix + "raw_inner_coefficients"),
                H("Exact three-index numerator formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every signed native inverse coefficient equals the sum of innerWeight times the original signed numerator coefficient over innerFiber. The finite antidiagonal convolution is reindexed by u=r+l and v=r+j only under both cumulative guards. The native numerator chart then supplies all three original exponent constraints, including negative and unsorted branches. No infinite sums are rearranged and the numerator may be infinite."))), DescribeRole.Theorem))));
}
