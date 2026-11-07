using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts;

internal sealed class PreparedEJMCompleteRawCut00000Part000035Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000035.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original context replay part 000035",
        H("Original context replay part 000035"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("These literal-node and acceptance facts support the corresponding accepted_actual_context root and its raw cut response. They are local steps of that consumer proof.")),
            Node("node-16-165", "node_16_165", "Literal node 165 at remaining fuel 5",
                "The original decoder equals the complete split at coordinate 16, with value children 0, 1, 2 and 3 at original indices 155, 159, 164, 29. The proof applies checked_split_node and reduces its finite check.", DescribeRole.Theorem),
            Node("accepted-16-21-165", "accepted_16_21_165", "Accepted occurrence at depth 16, code 21, node 165",
                "The conclusion is original Accepted at depth 16, full code 21 and original index 165, with remaining fuel 5. Assembly uses the literal split and every value branch, respectively accepted_17_84_155, accepted_17_85_159, accepted_17_86_164, accepted_17_87_29.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
