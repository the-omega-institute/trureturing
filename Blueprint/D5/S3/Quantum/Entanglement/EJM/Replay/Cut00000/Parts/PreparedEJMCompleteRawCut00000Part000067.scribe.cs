using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000067Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000067.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000067",
        H("Original context replay part 000067"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-15-330", "node_15_330", "Literal node 330 at remaining fuel 6",
                "The original decoder equals the complete split at coordinate 15, with value children 0, 1, 2 and 3 at original indices 111, 306, 329, 54. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-15-21-330", "accepted_15_21_330", "Accepted occurrence at depth 15, code 21, node 330",
                "The conclusion is original Accepted at depth 15, full code 21 and original index 330, with remaining fuel 6. Assembly uses the literal split and every value branch, respectively accepted_16_84_111, accepted_16_85_306, accepted_16_86_329, accepted_16_87_54.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
