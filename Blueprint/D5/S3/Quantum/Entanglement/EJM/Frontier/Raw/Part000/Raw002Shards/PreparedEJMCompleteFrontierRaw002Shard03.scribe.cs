using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw002Shards;

internal sealed class PreparedEJMCompleteFrontierRaw002Shard03Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Shards/PreparedEJMCompleteFrontierRaw002Shard03.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix contexts and responses 002Shard03",
        H("Original suffix contexts and responses 002Shard03"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The module supplies 16 original suffix acceptance declarations and 0 canonical response declarations. Raw suffix acceptance is consumed by response_of_raw, while the responses are leaves of the complete cut table response assembly.")),
            Node("raw-cut-00304", "raw_cut_00304", "Original suffix at depth 13, code 5158, node 16264",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 13, code 5158 and original node 16264. Its checker retains remaining fuel 8, the full prefixCache and full prefixPartial. The proof unfolds Accepted and reduces the original cached suffix check at these exact inputs.", DescribeRole.Theorem),
            Node("raw-cut-00319", "raw_cut_00319", "Original suffix at depth 14, code 20662, node 16686",
                "The statement is EJMOriginalReplayAssembly.Accepted at depth 14, code 20662 and original node 16686. Its checker retains remaining fuel 7, the full prefixCache and full prefixPartial. The proof unfolds Accepted and reduces the original cached suffix check at these exact inputs.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
