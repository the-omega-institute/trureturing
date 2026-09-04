using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class StatementDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.riemannVonMangoldt";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The main term and local count assemble the canonical Riemann-von Mangoldt certificate.",
            H("Riemann-von Mangoldt Statement"),
            Blocks(Describe.Lean(
                DescribeId.Create("statement"),
                DeclarationHandle.Create(Declaration),
                H("Riemann-von Mangoldt Statement"),
                StatementSource.FromAuthor(Disp(F.Id("Statement"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The main term and local count assemble the canonical Riemann-von Mangoldt certificate."))),
                DescribeRole.Theorem))));
    }
}
