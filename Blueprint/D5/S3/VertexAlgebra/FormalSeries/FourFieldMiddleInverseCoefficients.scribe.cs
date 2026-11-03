using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class FourFieldMiddleInverseCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleInverseCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("FourFieldMiddleInverseCoefficients", H("FourFieldMiddleInverseCoefficients"), Blocks(
            Describe.Lean(DescribeId.Create("fourfieldmiddleinversecoefficients-raw-middle-coefficients"), DeclarationHandle.Create(Prefix + "raw_middle_coefficients"),
                H("Native derivation of the finite readout"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three-index N3 balanced inverse is composed with the four outer binomial indices. Native finite coefficient convolutions prove the exact seven-index formula, shifts and signs. Wrong cumulative indices and negative original numerator inputs contribute zero."))), DescribeRole.Theorem))));
}
