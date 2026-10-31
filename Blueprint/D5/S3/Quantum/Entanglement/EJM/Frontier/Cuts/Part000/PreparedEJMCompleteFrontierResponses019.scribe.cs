using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cuts.Part000;

internal sealed class PreparedEJMCompleteFrontierResponses019Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cuts/Part000/PreparedEJMCompleteFrontierResponses019.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic responses for original cut table chunk 019",
        H("Semantic responses for original cut table chunk 019"),
        Blocks(
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Paragraph(Text("The proof follows the full binary tree of tableChunk019 and supplies 256 leaf responses in its stored order, starting with response_cut_42415 and ending with response_cut_43642. Both sides of every table branch are included.")),
            Node("table-chunk019-responses", "tableChunk019_responses", "Every leaf of tableChunk019 has its own response",
                "The conclusion is tableChunk019.Responses. The nested conjunction is built from the imported concrete response_cut declarations in the same order as the table leaves. Each component keeps its own prefix and original score; this conjunction is consumed by all_cut_responses.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
