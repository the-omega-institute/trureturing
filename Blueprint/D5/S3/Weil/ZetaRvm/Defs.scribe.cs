using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.halfContour_add";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The right-half contour and its additive law are fixed.",
            H("Riemann-von Mangoldt Definitions"),
            Blocks(Describe.Lean(
                DescribeId.Create("defs"),
                DeclarationHandle.Create(Declaration),
                H("Riemann-von Mangoldt Definitions"),
                StatementSource.FromAuthor(Disp(F.Id("Defs"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The right-half contour and its additive law are fixed."))),
                DescribeRole.Theorem))));
    }
}
