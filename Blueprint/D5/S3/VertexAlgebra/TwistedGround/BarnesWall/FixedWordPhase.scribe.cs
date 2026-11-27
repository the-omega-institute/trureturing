using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallFixedWordPhaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-vector phases of Barnes–Wall Pauli involutions",
        H("The exceptional phase vanishes on fixed lattice vectors"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-fixed-word-phase"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/BarnesWall/FixedWordPhase.half_gram_phase_zero_of_involution"),
            H("The triangular half-Gram corrections cancel"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The two integral tail quotients carry complementary quadratic forms. The " +
                "Pauli word pulls back each form by its square sign. On a fixed vector, " +
                "this either kills an individual triangular correction or makes the two " +
                "corrections equal in characteristic two."))),
            DescribeRole.Theorem))));
}
