using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMExactCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMExactCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual exact EJM triangle nonlocality certificate",
        H("The actual exact EJM triangle nonlocality certificate"),
        Blocks(
            Paragraph(Text("The coefficients and original marginal maps are those of Gitton and Renner's pinned ejm_224_nl_certificate experiment. Every concrete local row, complete terminal event, contraction and context-specific global branch must earn its own Lean acceptance. External producer checks or minima are not premises. This consumer supplies no local-model, coefficient-amplitude or score-positivity assumption.")),
            Describe.Lean(DescribeId.Create("actual-margin"),
                DeclarationHandle.Create(Prefix + "score_lower_bound"), H("An earned positive margin on every event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact integer score of every original twenty-node, four-outcome event is at least the positive scale 6987435. This derives from complete local acceptance and exhaustive replay in the actual partial context."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonlocality"),
                DeclarationHandle.Create(Prefix + "result"), H("Refute the original continuous triangle local model"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The global positive score contradicts the zero expectation of the same score under every measurable triangle local model with three independent sources. The conclusion refers to the original EJM probability law, with its recorded party order. Source registration remains unfinished under issue #16309."))), DescribeRole.Theorem))));
}
