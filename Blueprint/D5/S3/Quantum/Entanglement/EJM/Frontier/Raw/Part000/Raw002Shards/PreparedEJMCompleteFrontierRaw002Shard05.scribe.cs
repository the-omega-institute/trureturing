using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw002Shards;

internal sealed class PreparedEJMCompleteFrontierRaw002Shard05Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Shards/PreparedEJMCompleteFrontierRaw002Shard05.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fifteen retained Raw002 shard-five contexts",
        H("The fifteen retained Raw002 shard-five contexts"),
        Blocks(
            Paragraph(Text("These source candidates preserve the original mathematical declarations and proof bodies. Metadata and Scribe preparation alone does not establish kernel acceptance, scoped-report acceptance, emission, complete producer acceptance or a global EJM score bound.")),
            Paragraph(Text("The source file determines declaration GIDs. Existing Lean namespaces and proof attribution are retained; an imported declaration is described by its actual source owner.")),
            Paragraph(Text("This shard owns fifteen Raw declarations. The original raw_cut_00337 name and type are retained by Frontier/Raw/Part000/Raw002Tail442/Assembly, imported here. The unchanged Raw002 facade owns response_cut_00337 and consumes that Raw result; no second wrapper or duplicate Raw theorem is introduced.")),
            Paragraph(Text("The existing Raw002 response collection feeds Responses110, the complete response collection and PreparedEJMCompleteFrontierRoot.original_score_lower_bound. Preserving this consumption path does not assert that every producer has compiled.")),
            Node("raw-cut-00336", "raw_cut_00336", "Original complete-context acceptance: raw_cut_00336",
                "Depth 13, base-four prefix 5208 and literal DAG node 17358 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00338", "raw_cut_00338", "Original complete-context acceptance: raw_cut_00338",
                "Depth 13, base-four prefix 5210 and literal DAG node 17454 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00339", "raw_cut_00339", "Original complete-context acceptance: raw_cut_00339",
                "Depth 13, base-four prefix 5211 and literal DAG node 17480 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00340", "raw_cut_00340", "Original complete-context acceptance: raw_cut_00340",
                "Depth 12, base-four prefix 1303 and literal DAG node 893 fix fuel 9, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00341", "raw_cut_00341", "Original complete-context acceptance: raw_cut_00341",
                "Depth 12, base-four prefix 1304 and literal DAG node 1738 fix fuel 9, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00342", "raw_cut_00342", "Original complete-context acceptance: raw_cut_00342",
                "Depth 13, base-four prefix 5220 and literal DAG node 17524 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00343", "raw_cut_00343", "Original complete-context acceptance: raw_cut_00343",
                "Depth 13, base-four prefix 5221 and literal DAG node 17570 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00344", "raw_cut_00344", "Original complete-context acceptance: raw_cut_00344",
                "Depth 13, base-four prefix 5222 and literal DAG node 17607 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00345", "raw_cut_00345", "Original complete-context acceptance: raw_cut_00345",
                "Depth 13, base-four prefix 5223 and literal DAG node 17629 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00346", "raw_cut_00346", "Original complete-context acceptance: raw_cut_00346",
                "Depth 13, base-four prefix 5224 and literal DAG node 17676 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00347", "raw_cut_00347", "Original complete-context acceptance: raw_cut_00347",
                "Depth 13, base-four prefix 5225 and literal DAG node 17729 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00348", "raw_cut_00348", "Original complete-context acceptance: raw_cut_00348",
                "Depth 13, base-four prefix 5226 and literal DAG node 17762 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00349", "raw_cut_00349", "Original complete-context acceptance: raw_cut_00349",
                "Depth 13, base-four prefix 5227 and literal DAG node 17776 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00350", "raw_cut_00350", "Original complete-context acceptance: raw_cut_00350",
                "Depth 13, base-four prefix 5228 and literal DAG node 17819 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."),
            Node("raw-cut-00351", "raw_cut_00351", "Original complete-context acceptance: raw_cut_00351",
                "Depth 13, base-four prefix 5229 and literal DAG node 17876 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
