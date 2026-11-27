using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class CharacterLevelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character Levels", H("Character Levels"),
        Blocks(
            Paragraph(Text("Rational and tame-level points of U(1); finiteness of its ray class group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharacterLevels.exists_divStar"),
                H("exists_divStar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hilbert 90 for finite ideles: for every norm-one adele u of the CM field E there is a finite idele y such that the finite part of u equals y/ȳ.")))))));
}
