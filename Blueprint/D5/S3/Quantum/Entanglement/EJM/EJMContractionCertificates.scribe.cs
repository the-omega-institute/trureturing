using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMContractionCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMContractionCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact contraction premises for the actual EJM locality refutation.",
        H("Original head sums at every stored tail representative"),
        Blocks(
            Paragraph(Text("The numerical receipts evaluate the original coefficient functions at every head assignment of each explicit tail representative. Finite chunks cover the entire representative domains; the public interval dispatch consumes every chunk. These values become useful through the earned contraction symmetries and terminal-bound soundness, then full local acceptance and the actual-context cache lower bound. External contraction calculations supply the proposed integers but supply no proof premise. The numerical receipts are consumed helpers in the same local cache soundness delivery.")),
            Describe.Lean(DescribeId.Create("triangle-contractions"),
                DeclarationHandle.Create(Prefix + "triangle_contractions"),
                H("All 95 exact triangle-tail contractions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every one of the 95 literal seven-tail representatives, the sum of all 64 original F1 head values weighted by the actual integer EJM numerator equals its stored contraction value. This is the complete numerical premise used by triangle terminal-bound soundness."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-contractions"),
                DeclarationHandle.Create(Prefix + "singleton_contractions"),
                H("All 332 exact singleton-tail contractions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every one of the 332 literal eight-tail representatives, the sum of the four original F2 head values equals its stored contraction value. The factor 64 belongs to the separate singleton centered score and remains present in its terminal inequality."))),
                DescribeRole.Theorem))));
}
