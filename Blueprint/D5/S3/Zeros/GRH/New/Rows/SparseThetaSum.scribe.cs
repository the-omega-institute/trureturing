using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class SparseThetaSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse Theta Sum", H("Sparse Theta Sum"),
        Blocks(
            Paragraph(Text("Crude formal degree bound; rotation argument isolating a value at a point where |F| is at least half its supremum. Sparse theta sums approximate a matrix coefficient; first minimum of Hom lattices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/SparseThetaSum.norm_modKernel_sub_realInner_le"),
                H("norm_modKernel_sub_realInner_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Sparse theta sums. Let c ≠ 0, cα𝔪Ô ⊆ Ô, 0 < m, m|τc| ≤ √(2π Im τȷ)·λ_{Hom(S,T)}(g,h) for all τ, q > fnn′, Q homogeneous of degree d. Then for some Ψ mod 𝔪, θ[Ψ,Q](gu,hu′) is within (100(d+2q)/m²)^q(‖u‖‖u′‖)^{3q}‖v_Q‖² of ⟨v_Q, Ω(u,u′)v_Q⟩ for all real u, u′.")))))));
}
