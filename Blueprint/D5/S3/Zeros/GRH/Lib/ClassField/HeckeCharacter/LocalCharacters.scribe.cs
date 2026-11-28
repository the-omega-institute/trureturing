using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class LocalCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Characters", H("Local Characters"),
        Blocks(
            Paragraph(Text("Global characters of the determinant read through local components at chosen places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LocalCharacters.localChar_det"),
                H("localChar_det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For finite adelic unitary g, localChar P ξ k at the determinant of the P-components of g equals ξ(d)|d|^{k/2}, d the idele that is det g at P and 1 elsewhere.")))))));
}
