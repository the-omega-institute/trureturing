using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallTensorIntertwinersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Covariant quaternion operators on the Barnes–Wall ground space",
        H("The reflection quotient realizes the uniform trace detector"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-tensor-intertwiners"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorIntertwiners.exists_tensor_intertwiners"),
            H("The normalized product trace is the tensor Gauss sum"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "Pairing complementary subset rows balances the scaling of their triangular incidence matrix. " +
                "The unimodular Gram gives the reflection-quotient ground representation. " +
                "The two quaternion displacements and their fixed spaces coincide with the even-row subspace. " +
                "The lifted intertwiners then have product trace governed by the spectator pairing."))),
            DescribeRole.Theorem))));
}
