using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class OscillatorPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Oscillator Pair", H("Oscillator Pair"),
        Blocks(
            Paragraph(Text("Derivative of oscillator representation on polynomial vectors is the quadratic creation-annihilation operator. Real unitary dual pair on Fock space: unitarity, derivative, positivity on harmonics.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/OscillatorPair.oscillatorPair_detTwist"),
                H("oscillatorPair_detTwist"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("On the Fock space of R×C matrices with signs ε_rε′_c, the representations h ↦ (det h)^γ ω(x ↦ hx) of U(ε) and g ↦ (det g)^γ′ ω(x ↦ xg⁻¹) of U(ε′) form a OscillatorPair with σ = 1 and constants γ, γ′ + |R| (FockDualPair.std).")))))));
}
