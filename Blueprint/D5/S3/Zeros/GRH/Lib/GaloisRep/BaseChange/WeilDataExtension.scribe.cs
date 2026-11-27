using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class WeilDataExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weil Data Extension", H("Weil Data Extension"),
        Blocks(
            Paragraph(Text("An adelic polynomial root of the norm can be corrected to a rational one. Splitting data for the Weil representation pass to suitably unramified CM extensions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/WeilDataExtension.nonempty_weilData_of_unramified"),
                H("nonempty_weilData_of_unramified"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If E carries Weil data, so does every stably unramified CM extension L with compatible CM type such that no place v = v̄ of L divides the relative different.")))))));
}
