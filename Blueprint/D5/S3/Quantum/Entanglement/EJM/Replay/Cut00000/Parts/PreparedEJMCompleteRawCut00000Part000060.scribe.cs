using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000060Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000060.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000060",
        H("Original context replay part 000060"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-13-292", "node_13_292", "Literal node 292 at remaining fuel 8",
                "The original decoder equals the complete split at coordinate 13, with value children 0, 1, 2 and 3 at original indices 110, 289, 290, 291. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-13-0-292", "accepted_13_0_292", "Accepted occurrence at depth 13, code 0, node 292",
                "The conclusion is original Accepted at depth 13, full code 0 and original index 292, with remaining fuel 8. Assembly uses the literal split and every value branch, respectively accepted_14_0_110, accepted_14_1_289, accepted_14_2_290, accepted_14_3_291.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
