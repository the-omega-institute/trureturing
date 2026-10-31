using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000008Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000008.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000008",
        H("Original context replay part 000008"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-15-55", "node_15_55", "Literal node 55 at remaining fuel 6",
                "The original decoder equals the complete split at coordinate 15, with value children 0, 1, 2 and 3 at original indices 30, 52, 53, 54. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-15-0-55", "accepted_15_0_55", "Accepted occurrence at depth 15, code 0, node 55",
                "The conclusion is original Accepted at depth 15, full code 0 and original index 55, with remaining fuel 6. Assembly uses the literal split and every value branch, respectively accepted_16_0_30, accepted_16_1_52, accepted_16_2_53, accepted_16_3_54.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
