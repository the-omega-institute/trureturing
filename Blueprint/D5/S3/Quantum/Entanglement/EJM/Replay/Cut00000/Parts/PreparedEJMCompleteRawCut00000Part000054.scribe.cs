using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000054Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000054.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000054",
        H("Original context replay part 000054"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-16-287", "node_16_287", "Literal node 287 at remaining fuel 5",
                "The original decoder equals the complete split at coordinate 16, with value children 0, 1, 2 and 3 at original indices 258, 268, 285, 286. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-16-27-287", "accepted_16_27_287", "Accepted occurrence at depth 16, code 27, node 287",
                "The conclusion is original Accepted at depth 16, full code 27 and original index 287, with remaining fuel 5. Assembly uses the literal split and every value branch, respectively accepted_17_108_258, accepted_17_109_268, accepted_17_110_285, accepted_17_111_286.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
