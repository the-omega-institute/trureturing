using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class IndexTypesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Index Types", H("Index Types"),
        Blocks(
            Paragraph(Text("Different generator and root discriminant lie between x^10 and x^12. Chosen places above g, tame characters there, base characters and pairs for the data. Row parameter, level prime N and its size, tame twists, characters of the lifts. Index types, signs, parameters, level group and good idempotent for the proof's spaces.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/IndexTypes.card_rowIndex"),
                H("card_rowIndex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The basis index set Data.RowIndex of Y₀ has exactly r elements, r the rank parameter of the data.")))))));
}
