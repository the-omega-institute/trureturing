using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class VirtualCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Virtual Characters", H("Virtual Characters"),
        Blocks(
            Paragraph(Text("Basic properties of characters and virtual characters of finite groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/VirtualCharacters.mem_virtualChars"),
                H("mem_virtualChars"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every character of a group G lies in the S-span virtualChars S G of the characters of G.")))))));
}
