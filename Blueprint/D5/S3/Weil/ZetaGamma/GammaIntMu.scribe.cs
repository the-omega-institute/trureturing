using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class GammaIntMuDocument : IScribeDocumentDefinition
{
    private const string Declaration = "Zeta23.MuInts.int_mu_of_stirling";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The Stirling estimate yields the first and second dyadic mu-integral asymptotics.",
            H("Gamma Integral Estimates"),
            Blocks(Describe.Lean(
                DescribeId.Create("gammaintmu"),
                DeclarationHandle.Create(Declaration),
                H("Gamma Integral Estimates"),
                StatementSource.FromAuthor(Disp(F.Id("GammaIntMu"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Stirling estimate yields the first and second dyadic mu-integral asymptotics."))),
                DescribeRole.Theorem))));
    }
}
