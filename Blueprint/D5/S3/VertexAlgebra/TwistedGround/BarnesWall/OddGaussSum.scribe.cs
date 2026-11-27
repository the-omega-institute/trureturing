using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallOddGaussSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Barnes–Wall quaternion trace Gauss sum",
        H("The actual quaternion lifts have positive Gauss sum in odd rank"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-odd-rank-quaternion-gauss"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum.tensor_trace_gauss_sum"),
            H("A spectator slot puts the trace phase in split form"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The normalized tensor Gram pairs an even row with its complementary odd row. " +
                "The two Pauli preimages give a complement permutation followed by a square-zero shear. " +
                "The half Gram vanishes within the two active slots, so the phase has zero basis values. " +
                "The resulting split quadratic character sum is positive for every odd slot count at least five."))),
            DescribeRole.Theorem))));
}
