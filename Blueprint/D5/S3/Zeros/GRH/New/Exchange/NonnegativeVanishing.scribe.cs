using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class NonnegativeVanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative Vanishing", H("Nonnegative Vanishing"),
        Blocks(
            Paragraph(Text("Theta integral coefficient vanishes at forms not negative definite, by circle weights.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/NonnegativeVanishing.centreCoeff_eq_zero_of_not_negative"),
                H("centreCoeff_eq_zero_of_not_negative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let X split over Z along b lines, Y have a positive sign and b more negative signs than Z, and weights of ν be below the number of positive signs of Z. For integrable terms, the theta integral with characters νυ^b has coefficient 0 at invertible T with ȷ⁻¹T not totally negative.")))))));
}
