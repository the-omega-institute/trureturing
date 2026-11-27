using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class ConjugatesOfJetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugates Of Jets", H("Conjugates Of Jets"),
        Blocks(
            Paragraph(Text("Standard data: stability, and p-adic bounds transfer from theta products to their jets. Scaled jets of standard theta data are integral at every prime. One theta lift raises valuations by the bound on jets of standard data. Galois conjugation of theta jets as semilinear map on Weil space, with size bounds.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/ConjugatesOfJets.exists_semilinear_isJetConjugate"),
                H("exists_semilinear_isJetConjugate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Conjugates of jets. For V standard of rank n, R ∩ R̄ = ∅ and σ ∈ Aut(ℂ/K), there are |t|² = 1/Ω, c ≠ 0, a norm-one finite adele z and a σ-semilinear L such that: for f in 𝒲_f and finite g, σ(T_per f) = T_t(Lf) (places permuted) and Lω(g)f = (σΔ(g)/Δ(g))ω(g)Lf; |Lϱ(αx)ω(g)θ°| ≤ exp(C(N₁n+1)²) everywhere, C = Parameters.c; L(Ψ⊗vac) = cω(z)(σΨ⊗vac) for Ψ Schwartz–Bruhat above R. Here T_a = Space.jetSeries a and per = Parameters.jetScale.")))))));
}
