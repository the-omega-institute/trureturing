using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallCoherentTraceSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Excluding the nonzero quaternion anomaly candidate",
        H("Excluding the nonzero quaternion anomaly candidate"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-coherenttracesign"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/CoherentTraceSign.zero_candidate_of_modular_identity"),
            H("The normalized modular identity excludes the nonzero candidate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The literal charge covariance equations give a positive product of the three " +
                "coherent ground traces. The cyclic modular normalization fixes each cyclic " +
                "ground trace at 2^32. Transport by the binary carry cochain changes all three " +
                "signs together, so the candidate exponent vanishes."))),
            DescribeRole.Theorem))));
}
