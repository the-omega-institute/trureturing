using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMJointWickDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint Wick evaluation of the original four inverse-lowered words",
        H("Joint Wick Evaluation"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-marked-gaussian-slot-words"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMJointWick.marked_gaussian_slot_words"),
            H("Simultaneous marked coefficient and the slot words"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The marked affine coefficient equals the native factorial "
                + "evaluation of all slot words in one Gaussian. Moving a pending mark into "
                + "the native polynomial keeps mixed-puncture edges and accounts for the "
                + "additional contractions within that mark's own slot."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-radial-physical-selected-occupation"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMJointWick.radial_physical_selected_occupation"),
                H("Original radial Gaussian after physical Taylor selection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed means and every covariance block on the radial "
                    + "A and B charts give the literal native Gaussian after the four "
                    + "inverse-lowered words. The extra same-slot term is the original Gram "
                    + "entry times the Taylor correction."))), DescribeRole.Theorem))));
}
