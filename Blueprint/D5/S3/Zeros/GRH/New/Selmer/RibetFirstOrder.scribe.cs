using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RibetFirstOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ribet First Order", H("Ribet First Order"),
        Blocks(
            Paragraph(Text("Fitting ideal of one character contains ∏X_j times a polynomial with bounded constant term. Abstract first-order Ribet lemma with congruent blocks, ties and Fitting ideal bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RibetFirstOrder.ribet_first_order"),
                H("ribet_first_order"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Ribet's lemma to first order: on 𝓧, u_x is a block plus characters ξ_e, ξ_0 = 1; β_x is the determinant of the combination ribetNormaliser of the u_x(g) − 1. Some f in S has fβ ∈ 𝒥; on 𝓧, β = 0 and f has no term properly dividing ∏X_j; that coefficient at π has valuation ≤ b₀ + Σ b_e + explicit losses.")))))));
}
