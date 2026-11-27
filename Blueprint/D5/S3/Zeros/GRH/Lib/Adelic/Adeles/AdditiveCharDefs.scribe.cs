using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class AdditiveCharDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Additive Char Defs", H("Additive Char Defs"),
        Blocks(
            Paragraph(Text("Standard additive character of the adeles; normalised Haar measures; topological instances.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharDefs.volume_Ô"),
                H("volume_Ô"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For the chosen Haar measure on the finite adeles of E, the ring Ô of integral finite adeles has volume 2^{r₂}/√|disc E|.")))))));
}
