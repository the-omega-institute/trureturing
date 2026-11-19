using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMOccupationTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original four-point sources in the common physical coordinate",
        H("Physical Four-Point Source Transport"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-signed-physical-source-transport"),
            DeclarationHandle.Create(Prefix + "signed_physical_source_transport"),
            H("Signed half-current source germs"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The inverse local coordinate and its half-current Jacobian "
                + "give a common squared source at each of P, Q, R and S. The lifted source at "
                + "the origin fixes the germ sign, with S reversed in B and Q and R reversed in D."))),
            DescribeRole.Theorem))));
}
