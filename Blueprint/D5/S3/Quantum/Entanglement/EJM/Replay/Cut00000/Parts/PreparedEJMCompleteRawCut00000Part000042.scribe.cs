using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000042Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000042.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000042",
        H("Original context replay part 000042"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-15-213", "node_15_213", "Literal node 213 at remaining fuel 6",
                "The original decoder equals the complete split at coordinate 15, with value children 0, 1, 2 and 3 at original indices 111, 165, 212, 54. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-15-5-213", "accepted_15_5_213", "Accepted occurrence at depth 15, code 5, node 213",
                "The conclusion is original Accepted at depth 15, full code 5 and original index 213, with remaining fuel 6. Assembly uses the literal split and every value branch, respectively accepted_16_20_111, accepted_16_21_165, accepted_16_22_212, accepted_16_23_54.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
