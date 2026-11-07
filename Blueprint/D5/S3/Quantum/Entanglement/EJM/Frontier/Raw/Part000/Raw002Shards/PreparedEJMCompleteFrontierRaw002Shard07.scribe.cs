using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw002Shards;

internal sealed class PreparedEJMCompleteFrontierRaw002Shard07Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Shards/PreparedEJMCompleteFrontierRaw002Shard07.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 002Shard07",
        H("Original suffix contexts and responses 002Shard07"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 16 original suffix acceptance declarations and 0 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Node("raw-cut-00368", "raw_cut_00368", "Original suffix at depth 13, code 5276, node 18413",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 5276 and original node 18413. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof unfolds Accepted and reduces the original cached suffix check at these exact inputs.", DescribeRole.Theorem),
            Node("raw-cut-00383", "raw_cut_00383", "Original suffix at depth 12, code 1325, node 1738",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 12, code 1325 and original node 1738. Its checker retains remaining fuel 9, the full prefixCache and full prefixPartial. The proof unfolds Accepted and reduces the original cached suffix check at these exact inputs.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
