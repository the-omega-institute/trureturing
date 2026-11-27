using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class ExtensionByZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extension By Zero", H("Extension By Zero"),
        Blocks(
            Paragraph(Text("Projection of finite adeles to finitely many places has a continuous additive section.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/ExtensionByZero.adeleOfLocal"),
                H("adeleOfLocal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Extension by zero: the additive and multiplicative map from the product of the E_w, w in P, to the finite adeles, with component 0 outside P.")))))));
}
