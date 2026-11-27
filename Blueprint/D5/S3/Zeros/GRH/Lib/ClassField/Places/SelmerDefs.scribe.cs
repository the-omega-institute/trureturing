using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class SelmerDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selmer Defs", H("Selmer Defs"),
        Blocks(
            Paragraph(Text("Complex conjugation, anticyclotomic characters, Selmer cocycles, Tate twists, odd Sha: definitions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/SelmerDefs.cmConj_algebraMap"),
                H("cmConj_algebraMap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a CM field E embedded in Ω, the chosen complex conjugation of Ω restricts to the complex conjugation of E.")))))));
}
