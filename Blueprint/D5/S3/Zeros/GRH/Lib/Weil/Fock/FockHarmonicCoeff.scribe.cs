using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class FockHarmonicCoeffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fock Harmonic Coeff", H("Fock Harmonic Coeff"),
        Blocks(
            Paragraph(Text("Functional bounded by its small-shift differences decays as any power of the shift. Fock inner product equals Fischer product; polynomials dense; intertwining relations for coefficients. Matrix coefficients of the oscillator representation between harmonic polynomials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/FockHarmonicCoeff.fockMatrixCoeff_eq_realInner"),
                H("fockMatrixCoeff_eq_realInner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let u in U(ε) be block diagonal for labels d, and ∂_i∂_j kill P, Q whenever d_i = d_j, ε_i ≠ ε_j. Then ⟨v_Q, ω₀(u)v_P⟩ = (det u₋)⁻¹⟨v_Q′, v_P⟩, u₋ the negative block, Q′ = Q under X_j ↦ ∑_i A_ij X_i, A = (complexLinearPart u)⁻¹.")))))));
}
