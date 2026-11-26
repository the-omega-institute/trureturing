using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class BarnesWallQ8CohomologyDetectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quaternion detector for the Barnes–Wall anomaly candidate",
        H("A quaternion detector for the Barnes–Wall anomaly candidate"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-quaternion-cocycle-detector"),
            DeclarationHandle.Create("D5/S3/HomologicalAlgebra/BarnesWallQ8CohomologyDetector.etaClass_circle_ne_zero"),
            H("The inflated class is nonzero on the quaternion group"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(
                Paragraph(Text(
                    "The polynomial cocycle on the elementary abelian quotient of Q8 is pulled " +
                    "back to Q8 with circle coefficients. The evaluation on a seven-term " +
                    "normalized bar cycle is one half modulo the integers.")),
                Paragraph(Text(
                    "Two degenerate terms give a cycle in Mathlib's unnormalized complex. " +
                    "Its pairing with any coboundary vanishes, so the cocycle defines a " +
                    "nonzero element of the third group cohomology."))),
            DescribeRole.Theorem))));
}
