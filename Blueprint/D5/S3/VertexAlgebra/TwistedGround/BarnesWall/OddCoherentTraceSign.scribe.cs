using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallOddCoherentTraceSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic characters exclude the nonzero Barnes–Wall anomaly candidate",
        H("The cyclic characters exclude the nonzero Barnes–Wall anomaly candidate"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-odd-coherent-trace-sign"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddCoherentTraceSign.zero_candidate_of_uniform_modular_identity"),
            H("The cyclic characters exclude the nonzero Barnes–Wall anomaly candidate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "Two traces on an order-four subgroup enter through a finite Fourier exchange of the normalized modular matrix. " +
                "The order-four tensor defect determines the ground multiplicity, and the reflection oscillator product contributes one at the cusp. " +
                "Scalar-related quaternion actions differ by one global character, which cancels in the literal trace ratio. " +
                "The statement uses the normalized cyclic character matrix, the twisted oscillator formulas, and the identification of the reference action with the cyclic trace as inputs."))),
            DescribeRole.Theorem))));
}
