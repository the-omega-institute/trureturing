using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part001;

internal sealed class PreparedEJMCompleteFrontierResponses070Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part001/PreparedEJMCompleteFrontierResponses070.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic responses for original cut table chunk 070",
        H("Semantic responses for original cut table chunk 070"),
        Blocks(
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Paragraph(Text("The proof follows the full binary tree of tableChunk070 and supplies 256 leaf responses in its stored order, starting with response_cut_35501 and ending with response_cut_35879. Both sides of every table branch are included.")),
            Node("table-chunk070-responses", "tableChunk070_responses", "Every leaf of tableChunk070 has its own response",
                "The conclusion is tableChunk070.Responses. The nested conjunction is built from the imported concrete response_cut declarations in the same order as the table leaves. Each component keeps its own prefix and original score; this conjunction is consumed by all_cut_responses.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
