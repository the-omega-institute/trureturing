using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMFixedChargeWickDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-charge Wick transport at the four punctures",
        H("Independent native mode assignments"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-m-fixed-charge-wick-native-assignment"),
                DeclarationHandle.Create(Prefix + "physical_marked_coefficient_assign"),
                H("Fixed-charge marked coefficient as a Wick assignment sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice with unit Gram determinant and a word of distinct labels "
                    + "from a finite type, fix the charge, the puncture, colour and spatial degree at each "
                    + "occurrence, and a real chart argument strictly between zero and one. In A or B require "
                    + "the slit parameter to have norm less than one. In D use the true lip. The physical "
                    + "marked Taylor coefficient is the charge exponential times the ordered partition sum. "
                    + "The correction endpoints carry the signed scales and four within-puncture contraction "
                    + "factors. Every surviving occurrence independently selects a native mode through its "
                    + "requested degree, with the signed inverse jet weight and the native covariance and "
                    + "mean entries."))),
                DescribeRole.Theorem))));
}
