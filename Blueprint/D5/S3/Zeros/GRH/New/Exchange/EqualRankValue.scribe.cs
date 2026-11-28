using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class EqualRankValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal Rank Value", H("Equal Rank Value"),
        Blocks(
            Paragraph(Text("Removing hyperbolic planes from both sides preserves the exchange identity. Exchange identity for all partners, constant known up to the equal-rank constant lambda. Modulus of the equal-rank theta constant is a nonzero multiple of Hecke L-values.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/EqualRankValue.exists_equalRankThetaRatio_value"),
                H("exists_equalRankThetaRatio_value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let W have rank n = 2k + 2q, q negative signs, and weights μ ≥ k. Some rapid v and C ≠ 0 give |λ(v)|² = CΠ(n/2+1) on ℍ ⊕ W for all tame characters of weight μ (equalRankThetaRatio, lValueProdInt).")))))));
}
