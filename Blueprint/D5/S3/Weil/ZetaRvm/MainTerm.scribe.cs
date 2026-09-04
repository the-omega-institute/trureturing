using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class MainTermDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.rvM_main";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The dyadic multiplicity count has its classical main term and logarithmic error.",
            H("Riemann-von Mangoldt Main Term"),
            Blocks(Describe.Lean(
                DescribeId.Create("mainterm"),
                DeclarationHandle.Create(Declaration),
                H("Riemann-von Mangoldt Main Term"),
                StatementSource.FromAuthor(Disp(F.Id("MainTerm"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The dyadic multiplicity count has its classical main term and logarithmic error."))),
                DescribeRole.Theorem))));
    }
}
