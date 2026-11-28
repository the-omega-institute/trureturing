using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class LowRankIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low Rank Identity", H("Low Rank Identity"),
        Blocks(
            Paragraph(Text("Orbit terms of theta kernel with standard ramified datum at parabolic points. Slice of the standard datum factors over the two summands. Equal-rank theta integral is constant; exchange identity at top of the tower.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/LowRankIdentity.stdExchange_of_periods"),
                H("stdExchange_of_periods"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("StdExchange holds for X, V′ ⊕ W₁, V′ and ℓ = |l|²/Π(rk W₁/2) if the splittings are adapted, rk W₁ is even, v, v′ are rapid, slices of v integrate over [U(W₁)] to ρ·l(𝔠) times those of v′ up to the Levi factor (ρ ≥ 0, non-zero near 1), and a support or sign condition holds.")))))));
}
