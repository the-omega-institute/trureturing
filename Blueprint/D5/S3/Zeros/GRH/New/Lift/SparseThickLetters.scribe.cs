using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class SparseThickLettersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse Thick Letters", H("Sparse Thick Letters"),
        Blocks(
            Paragraph(Text("Polynomial in tame generator kills cokernel of Kisin modules independently of ramification index. Kummer chart of a tame extension of Q_p with a generator of tame inertia. Rank-free exponents killing cup products for two sizes and sparse thick letters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/SparseThickLetters.scaledCupBounds_sparse_thick"),
                H("scaledCupBounds_sparse_thick"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Sparse thick letters. Paired sides have jump sets in opposite windows [−η, η] ∪ ±[β_i, β_i + V], β_i = b or G, G + V ≤ η, no three β = b at gaps in [1, J]; signs constant, or unramified with p ≥ 7. Under size inequalities Lift.Pairing.ScaledCupBounds holds with exponent 10⁴X(J + 1).")))))));
}
