using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMNativeOccupationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Taylor selection in the original signed native Gaussian",
        H("Native Four-Point Occupation"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-native-selected-occupation"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccupation.native_selected_occupation"),
            H("Native signed mode selection"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The signed source and covariance modes give the literal "
                + "sewn Gaussian entries. Independent marking of the occurrences gives "
                + "the affine occupation with the product of its original factorials."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-selected-radial-physical-mean"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccupation.selected_radial_physical_mean"),
                H("Physical Taylor coefficient of the native signed mean"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The physical charge-linear source gives the original "
                    + "signed sewn mean in each surviving mode with its inverse-coordinate "
                    + "creator coefficient and the native chart period."))), DescribeRole.Theorem))));
}
