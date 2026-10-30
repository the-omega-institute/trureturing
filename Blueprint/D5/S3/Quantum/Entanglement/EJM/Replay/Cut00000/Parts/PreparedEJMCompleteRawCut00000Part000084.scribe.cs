using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000084Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000084.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000084",
        H("Original context replay part 000084"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-12-415", "node_12_415", "Literal node 415 at remaining fuel 9",
                "The original decoder equals the complete split at coordinate 12, with value children 0, 1, 2 and 3 at original indices 292, 412, 413, 414. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-12-0-415", "accepted_12_0_415", "Accepted occurrence at depth 12, code 0, node 415",
                "The conclusion is original Accepted at depth 12, full code 0 and original index 415, with remaining fuel 9. Assembly uses the literal split and every value branch, respectively accepted_13_0_292, accepted_13_1_412, accepted_13_2_413, accepted_13_3_414.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
