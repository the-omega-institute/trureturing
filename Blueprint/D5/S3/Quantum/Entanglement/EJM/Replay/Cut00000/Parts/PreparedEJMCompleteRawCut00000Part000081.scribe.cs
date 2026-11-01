using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000081Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000081.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000081",
        H("Original context replay part 000081"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-13-412", "node_13_412", "Literal node 412 at remaining fuel 8",
                "The original decoder equals the complete split at coordinate 13, with value children 0, 1, 2 and 3 at original indices 293, 377, 411, 291. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-13-1-412", "accepted_13_1_412", "Accepted occurrence at depth 13, code 1, node 412",
                "The conclusion is original Accepted at depth 13, full code 1 and original index 412, with remaining fuel 8. Assembly uses the literal split and every value branch, respectively accepted_14_4_293, accepted_14_5_377, accepted_14_6_411, accepted_14_7_291.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
