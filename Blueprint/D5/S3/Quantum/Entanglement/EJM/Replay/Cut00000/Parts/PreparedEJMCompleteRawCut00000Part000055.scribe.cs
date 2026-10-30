using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000055Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000055.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000055",
        H("Original context replay part 000055"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-15-288", "node_15_288", "Literal node 288 at remaining fuel 6",
                "The original decoder equals the complete split at coordinate 15, with value children 0, 1, 2 and 3 at original indices 111, 246, 247, 287. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-15-6-288", "accepted_15_6_288", "Accepted occurrence at depth 15, code 6, node 288",
                "The conclusion is original Accepted at depth 15, full code 6 and original index 288, with remaining fuel 6. Assembly uses the literal split and every value branch, respectively accepted_16_24_111, accepted_16_25_246, accepted_16_26_247, accepted_16_27_287.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
