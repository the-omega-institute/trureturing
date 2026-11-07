using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part000;

internal sealed class PreparedEJMCompleteFrontierResponses008Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part000/PreparedEJMCompleteFrontierResponses008.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic responses for original cut table chunk 008",
        H("Semantic responses for original cut table chunk 008"),
        Blocks(
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Paragraph(Text("The proof follows the full binary tree of tableChunk008 and supplies 256 leaf responses in its stored order, starting with response_cut_52369 and ending with response_cut_01901. Both sides of every table branch are included.")),
            Node("table-chunk008-responses", "tableChunk008_responses", "Every leaf of tableChunk008 has its own response",
                "The conclusion is tableChunk008.Responses. The nested conjunction is built from the imported concrete response_cut declarations in the same order as the table leaves. Each component keeps its own prefix and original score; this conjunction is consumed by all_cut_responses.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
