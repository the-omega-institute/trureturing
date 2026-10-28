using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldBalancedInverseCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact finite numerator formula", H("The exact finite numerator formula"), Blocks(
            Describe.Lean(DescribeId.Create("threefieldbalancedinversecoefficients-raw-balanced-coefficients"),
                DeclarationHandle.Create(Prefix + "raw_balanced_coefficients"),
                H("The exact finite numerator formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed native inverse equals the finite sum over the balanced numerator fiber with input (s+k-r-l,x+a0+a1+2k+r+j+l,z+a2-j). The finite convolution is reindexed by u=r+l and v=r+j+l after their cumulative guards are established. Signed outside-cone targets and unsorted numerator indices give zero without additional positivity assumptions."))), DescribeRole.Theorem))));
}
