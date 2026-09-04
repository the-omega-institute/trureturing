using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class GammaSideDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.RvM.gamma_side";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The folded Gamma logarithmic derivative equals the mu integral.",
            H("Riemann-von Mangoldt Gamma Side"),
            Blocks(Describe.Lean(
                DescribeId.Create("gammaside"),
                DeclarationHandle.Create(Declaration),
                H("Riemann-von Mangoldt Gamma Side"),
                StatementSource.FromAuthor(Disp(F.Id("GammaSide"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The folded Gamma logarithmic derivative equals the mu integral."))),
                DescribeRole.Theorem))));
    }
}
