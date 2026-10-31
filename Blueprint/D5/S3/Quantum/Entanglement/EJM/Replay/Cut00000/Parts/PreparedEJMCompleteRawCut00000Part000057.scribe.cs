using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000057Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000057.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000057",
        H("Original context replay part 000057"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-14-289", "node_14_289", "Literal node 289 at remaining fuel 7",
                "The original decoder equals the complete split at coordinate 14, with value children 0, 1, 2 and 3 at original indices 151, 213, 288, 109. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-14-1-289", "accepted_14_1_289", "Accepted occurrence at depth 14, code 1, node 289",
                "The conclusion is original Accepted at depth 14, full code 1 and original index 289, with remaining fuel 7. Assembly uses the literal split and every value branch, respectively accepted_15_4_151, accepted_15_5_213, accepted_15_6_288, accepted_15_7_109.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
