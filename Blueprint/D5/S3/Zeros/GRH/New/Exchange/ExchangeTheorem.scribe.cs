using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class ExchangeTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exchange Theorem", H("Exchange Theorem"),
        Blocks(
            Paragraph(Text("Exchange theorem for theta integrals of complementary rank. If the ranks and negative signs of hermitian spaces V, V' over a CM field add up to those of W (few negative), with rk V − rk V' = 2e ≥ 0, then theta integrals over U(V) and U(V') agree on matched ramified data up to a nonzero constant sized by the conductor and Hecke L-values at 1,…,e, so theta lifts can be exchanged. Equal theta lifts of characters of complementary groups are known for trivial characters (Siegel–Weil) and for O(3), O(1) to Mp(2). Related work: Snitz, Theta correspondence of automorphic characters (thesis), 2003; Erez, Matchings of theta lifts of automorphic characters, arXiv 2401.13469, 2024; Gan–Qiu–Takeda, The regularized Siegel–Weil formula (second term identity), 2014.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/ExchangeTheorem.exchange_theorem"),
                H("exchange_theorem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Exchange theorem: let rk W = n = rk V + rk V′, rk V = rk V′ + 2e, q_W = q_V + q_{V′} negative signs, n ≥ 2q_W + 2, μ ≥ n/2 − q_W, v rapid. Some C and rapid x give ∫_{[U(V)]}θ(x⊗Φ) = c∫_{[U(V′)]}θ(v⊗Ψ) for partners, c ≠ 0, |c|² = C·lValueProd, for each tame ν.")))))));
}
