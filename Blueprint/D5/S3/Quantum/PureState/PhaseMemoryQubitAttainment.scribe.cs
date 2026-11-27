using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseMemoryQubitAttainmentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit common qubit encoders for Walsh and symmetric Fourier phases.",
        H("Qubit strategies attaining the clipped score"),
        Blocks(
            Paragraph(Text("Put r = √(t₁² + t₂² + t₃²) > 0. Each construction sends the four input coordinates to an orthonormal operator basis, viewed as two-qubit vectors and divided by √2. Tracing out the second qubit gives the same CPTP encoder for every input. The coefficient matrix before the partial trace has the form (t₀I + Bⱼ)/√2 with Bⱼ Hermitian and traceless, Bⱼ² = r²I and ΣⱼBⱼ = 0. The positive-eigenvalue projector Rⱼ = (I + Bⱼ/r)/2 has trace one. The four effects Rⱼ/2 sum to I and yield score (t₀ + r)²/4.")),
            Describe.Lean(DescribeId.Create("qubit-walsh-four-attainment"),
                DeclarationHandle.Create(Module + "walsh4_attains"),
                H("The Pauli basis gives an attaining Walsh encoder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the coefficient matrices I, X, Y and Z in Walsh order. The Walsh signs make the last three coefficients real, and the Pauli anticommutation relations give Bⱼ² = r²I."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qubit-symmetric-fourier-four-attainment"),
                DeclarationHandle.Create(Module + "symmetric_fourier4_attains"),
                H("Equal conjugate-frequency amplitudes give an attaining Fourier encoder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use I, √2 E₀₁, Z and √2 E₁₀. At t₁ = t₃ the off-diagonal entries have conjugate Fourier phases with equal magnitude, so the tail is Hermitian. Its square is r²I, which gives the same decoder construction."))),
                DescribeRole.Theorem))));
}
