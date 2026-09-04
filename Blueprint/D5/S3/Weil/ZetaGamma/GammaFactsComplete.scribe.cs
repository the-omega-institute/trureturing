using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class GammaFactsCompleteDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.gammaFacts";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "All Gamma-side fields are assembled without hypotheses.",
            H("Complete GammaFacts Assembly"),
            Blocks(Describe.Lean(
                DescribeId.Create("gammafactscomplete"),
                DeclarationHandle.Create(Declaration),
                H("Complete GammaFacts Assembly"),
                StatementSource.FromAuthor(Disp(F.Id("GammaFactsComplete"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All Gamma-side fields are assembled without hypotheses."))),
                DescribeRole.Theorem))));
    }
}
