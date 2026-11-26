using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class FitTwistsExistDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fit Twists Exist", H("Fit Twists Exist"),
        Blocks(
            Paragraph(Text("Existence of twists, one per embedding, whose first m powers have few congruences.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/FitTwistsExist.exists_isFitFamily"),
                H("exists_isFitFamily"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("All data D have m-fold twists ϑ_ι, one for each prime ℓ and isomorphism ι: ℂ ≅ ℚ̄_ℓ, such that the family (ϑ_ι^n) is fit (Data.IsFitFamily) for 1 ≤ n ≤ m.")))))));
}
