using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw014Checkpoints;

internal sealed class PreparedEJMCompleteFrontierRaw014Literal20Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw014Checkpoints/PreparedEJMCompleteFrontierRaw014Literal20.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original Raw014 checkpoint Literal20",
        H("Exact original Raw014 checkpoint Literal20"),
        Blocks(
            Paragraph(Text("This checkpoint is consumed by the original Raw014 frontier facade and the original_score_lower_bound proof through its complete frontier dependency path.")),
            Paragraph(Text("All imports, namespaces, declarations, proofs and diagnostics are unchanged. Only the canonical production header is prepended. Metadata preparation does not establish acceptance of the new source bytes or the complete certificate.")),
            Node("accepted-d14-p75611-i60667", "accepted_d14_p75611_i60667", "Complete Accepted context at depth 14, prefix 75611 and node 60667",
                "The original Accepted proposition fixes depth 14, base-four prefix 75611 and literal DAG node 60667. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d14-p75562-i60515", "accepted_d14_p75562_i60515", "Complete Accepted context at depth 14, prefix 75562 and node 60515",
                "The original Accepted proposition fixes depth 14, base-four prefix 75562 and literal DAG node 60515. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
