using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class CuspidalFunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cuspidal Function", H("Cuspidal Function"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalFunction.isCuspidal_greenCuspidal"),
                H("isCuspidal_greenCuspidal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Adjoint of multiplication; it is a derivation for cuspidal functions (Zelevinsky). Möbius function (Steinberg) lives on semisimple classes; minus the Brauer lift divided by constOne is cuspidal.")))))));
}
