using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class BacklundDefsDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.mem_reZeroSet";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The real-part zero set used in Backlund's bound is fixed.",
            H("Backlund Definitions"),
            Blocks(Describe.Lean(
                DescribeId.Create("backlunddefs"),
                DeclarationHandle.Create(Declaration),
                H("Backlund Definitions"),
                StatementSource.FromAuthor(Disp(F.Id("BacklundDefs"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real-part zero set used in Backlund's bound is fixed."))),
                DescribeRole.Theorem))));
    }
}
