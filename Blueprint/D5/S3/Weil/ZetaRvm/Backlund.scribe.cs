using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class BacklundDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.backlund_horizontal";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The horizontal argument variation and vertical line are logarithmically controlled.",
            H("Backlund Horizontal Bound"),
            Blocks(Describe.Lean(
                DescribeId.Create("backlund"),
                DeclarationHandle.Create(Declaration),
                H("Backlund Horizontal Bound"),
                StatementSource.FromAuthor(Disp(F.Id("Backlund"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The horizontal argument variation and vertical line are logarithmically controlled."))),
                DescribeRole.Theorem))));
    }
}
