using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class ReZeroCountDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.reZeroSet_card_le";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Jensen theory bounds the real-part crossing count by a logarithmic term.",
            H("Jensen Real-Zero Count"),
            Blocks(Describe.Lean(
                DescribeId.Create("rezerocount"),
                DeclarationHandle.Create(Declaration),
                H("Jensen Real-Zero Count"),
                StatementSource.FromAuthor(Disp(F.Id("ReZeroCount"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Jensen theory bounds the real-part crossing count by a logarithmic term."))),
                DescribeRole.Theorem))));
    }
}
