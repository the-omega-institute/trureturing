using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallCyclicEtaTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic modular normalization of the Barnes–Wall trace",
        H("The cyclic modular normalization of the Barnes–Wall trace"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-cyclicetatrace"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/CyclicEtaTrace.cyclic_ground_trace_eq_two_pow_32"),
            H("The cyclic modular identity fixes the ground trace at 2^32"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The Dedekind S transformation cancels the square-root factors in the order-four " +
                "eta quotient. The remaining product tends to one at the cusp, which fixes the " +
                "ground coefficient once the normalized cyclic trace identity is supplied."))),
            DescribeRole.Theorem))));
}
