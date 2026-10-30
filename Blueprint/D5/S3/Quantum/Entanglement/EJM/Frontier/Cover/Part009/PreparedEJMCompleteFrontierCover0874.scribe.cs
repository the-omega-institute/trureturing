using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0874Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0874.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0874",
        H("Original frontier context coverage 0874"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41954", "selected_cut_41954", "Selected cut at depth 12, code 336992, node 985390",
                "At remaining fuel 9 and original index 985390, selection on the full partial prefix of depth 12 and code 336992 returns the complete row with depth 12, base-four code 336992, original node 985390, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42002", "selected_cut_42002", "Selected cut at depth 11, code 84269, node 1148336",
                "At remaining fuel 10 and original index 1148336, selection on the full partial prefix of depth 11 and code 84269 returns the complete row with depth 11, base-four code 84269, original node 1148336, kind 2, reserved field 0, 2737 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84248-1147083", "unmarked_context_11_84248_1147083", "Unmarked parent at depth 11, code 84248",
                "The frontier Boolean is false at remaining fuel 10, original node 1147083, the whole prefixCache at depth 11 and code 84248, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21066-1148262", "unmarked_context_10_21066_1148262", "Unmarked parent at depth 10, code 21066",
                "The frontier Boolean is false at remaining fuel 11, original node 1148262, the whole prefixCache at depth 10 and code 21066, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84248-1147083", "node_context_11_84248_1147083", "Original split at fuel 10 and node 1147083",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1147016, 1147055, 1147082. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21066-1148262", "node_context_10_21066_1148262", "Original split at fuel 11 and node 1148262",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1148180, 1148227, 1109453, 1148261. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336992-985390", "context_12_336992_985390", "Context at depth 12, code 336992, node 985390",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336992 and original node 985390, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-84269-1148336", "context_11_84269_1148336", "Context at depth 11, code 84269, node 1148336",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84269 and original node 1148336, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
