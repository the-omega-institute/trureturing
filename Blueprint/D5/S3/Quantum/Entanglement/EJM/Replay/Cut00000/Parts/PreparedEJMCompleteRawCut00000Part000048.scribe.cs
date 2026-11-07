using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000048Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000048.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000048",
        H("Original context replay part 000048"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-16-246", "node_16_246", "Literal node 246 at remaining fuel 5",
                "The original decoder equals the complete split at coordinate 16, with value children 0, 1, 2 and 3 at original indices 227, 230, 236, 245. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-16-25-246", "accepted_16_25_246", "Accepted occurrence at depth 16, code 25, node 246",
                "The conclusion is original Accepted at depth 16, full code 25 and original index 246, with remaining fuel 5. Assembly uses the literal split and every value branch, respectively accepted_17_100_227, accepted_17_101_230, accepted_17_102_236, accepted_17_103_245.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
