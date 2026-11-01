using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteFrontierResponsesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierResponses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Responses for every original cut table leaf",
        H("Responses for every original cut table leaf"),
        Blocks(
            Paragraph(Text("The full binary tree joins all 207 chunks, from chunk 000 through chunk 206, preserving each depth/code pivot and the complete row at each leaf. The response assembly has exactly the corresponding conjunction structure.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("all-cut-responses", "all_cut_responses", "Join the complete cut response conjunction",
                "The theorem concludes cutTable.Responses by pairing all 207 imported tableChunk response theorems in the tree order. lookup_response and frontier_responses consume this whole conjunction in the full original root argument.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
