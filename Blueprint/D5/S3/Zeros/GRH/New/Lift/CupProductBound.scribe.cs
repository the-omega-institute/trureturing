using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class CupProductBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cup Product Bound", H("Cup Product Bound"),
        Blocks(
            Paragraph(Text("a cup product of crystalline cocycles is a coboundary if they have lifts to W(C^♭)-coefficients whose Galois and Frobenius differences pair into W(𝔪^♭).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/CupProductBound.of_isSafe"),
                H("of_isSafe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let e₁ + e₂ + e₃ ≤ e, let x, w lie over p^{e₁}c and x' over p^{e₂}c'. If ((g−1)x, g(h−1)x'), (w−x, (g−1)x'), ((g−1)w, g(φ−1)x'), (φx−w, (g−1)φx') satisfy Lift.Pairing.IsSafe e₃ for all g, h in Γ', then Lift.Pairing.ScaledCupBounds holds for e, c, c'.")))))));
}
