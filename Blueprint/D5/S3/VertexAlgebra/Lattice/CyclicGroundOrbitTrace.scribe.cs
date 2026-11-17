using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class CyclicGroundOrbitTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cyclic ground-orbit power traces with the retained cocycle phase.",
        H("Trace of a Corrected Ground Charge Cycle"),
        Blocks(
            Paragraph(Text("For an integral symmetric even-diagonal lattice and an additive isometry preserving the bilinear form, take one actual first-return charge orbit of a norm-four ground state. The span of its distinct zero-oscillator ground vectors is finite and carries the corrected lift power.")),
            Paragraph(Text("The action on each orbit basis vector is the literal product of the one-step cocycle and sign phases. The trace is the sum of the phases exactly when the power returns the orbit, and is zero for a non-returning power because the cyclic shift has no diagonal entries.")),
            Describe.Lean(
                DescribeId.Create("corrected-ground-cycle-power-trace"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitTrace.corrected_ground_cycle_power_trace"),
                H("Returning powers have the literal phase sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof computes the actual LinearMap.trace in the finite orbit basis. It retains the correctedGroundPhase cocycle product and separates the divisibility case from the zero-trace non-returning case."))),
                DescribeRole.Theorem))));
}
