using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class SplittingCharExistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting Char Exists", H("Splitting Char Exists"),
        Blocks(
            Paragraph(Text("Existence of an unramified splitting Hecke character of a CM field.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/SplittingCharExists.nonempty_splittingChar"),
                H("nonempty_splittingChar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the CM field E be stably unramified (StablyUnram), and let every root of unity of E be δ/δ̄ for some unit δ with ∏_w Φ_w(δ) = 1. Then E has a splitting character (SplittingChar).")))))));
}
