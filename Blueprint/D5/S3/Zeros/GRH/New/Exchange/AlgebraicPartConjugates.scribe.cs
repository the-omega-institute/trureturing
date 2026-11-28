using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class AlgebraicPartConjugatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic Part Conjugates", H("Algebraic Part Conjugates"),
        Blocks(
            Paragraph(Text("Galois conjugate of the lift is the lift for the conjugate Hecke character. Galois conjugates of the lift's squared norm: factorials over periods, error bounded below.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/AlgebraicPartConjugates.log_norm_map_norm_sq_trivialLift"),
                H("log_norm_map_norm_sq_trivialLift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For σ in Aut(ℂ/K) and fixed n, one c serves all pairs (ν, z) with |n| = 2z ≥ 4: untwisted, log|σ(‖Ξ‖²)| = c + r + ∑_τ (log λ_τ! − λ_τ log(Ω/g)), λ_τ = c_τ − z, with r ≥ −4f, and r ≤ 4f if all λ_τ = 0.")))))));
}
