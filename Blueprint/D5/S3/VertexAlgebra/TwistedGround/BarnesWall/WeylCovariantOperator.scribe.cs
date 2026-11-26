using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallWeylCovariantOperatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A covariant operator from the binary Weyl sum",
        H("A covariant operator from the binary Weyl sum"),
        Blocks(Describe.Lean(
            DescribeId.Create("binary-weyl-covariant-operator"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/WeylCovariantOperator.exists_covariant_operator"),
            H("Existence with trace equal to the ground-space dimension"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The lift phase and bilinear cocycle make the coefficient of each displacement " +
                "independent of the preimage. Translating the displacement sum proves covariance. " +
                "The zero displacement gives the entire trace, so the operator is nonzero."))),
            DescribeRole.Theorem))));
}
