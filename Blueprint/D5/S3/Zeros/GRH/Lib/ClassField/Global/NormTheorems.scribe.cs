using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Global;

internal sealed class NormTheoremsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norm Theorems", H("Norm Theorems"),
        Blocks(
            Paragraph(Text("Surjectivity of Artin map, cyclic norm group, Hasse norm theorem for totally positive elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Global/NormTheorems.char_artinMap_eq_one_iff"),
                H("char_artinMap_eq_one_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let L/K be the extension cut out by the character χ. A finite idele a has χ(Art a) trivial exactly when a is a totally positive element of K^× times the norm of a finite idele of L.")))))));
}
