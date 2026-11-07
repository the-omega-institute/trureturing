using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000079Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000079.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000079",
        H("Original context replay part 000079"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-14-411", "node_14_411", "Literal node 411 at remaining fuel 7",
                "The original decoder equals the complete split at coordinate 14, with value children 0, 1, 2 and 3 at original indices 378, 407, 378, 410. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-14-6-411", "accepted_14_6_411", "Accepted occurrence at depth 14, code 6, node 411",
                "The conclusion is original Accepted at depth 14, full code 6 and original index 411, with remaining fuel 7. Assembly uses the literal split and every value branch, respectively accepted_15_24_378, accepted_15_25_407, accepted_15_26_378, accepted_15_27_410.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
