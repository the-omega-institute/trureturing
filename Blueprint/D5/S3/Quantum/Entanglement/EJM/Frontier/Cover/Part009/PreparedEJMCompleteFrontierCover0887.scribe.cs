using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0887Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0887.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0887",
        H("Original frontier context coverage 0887"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42579", "selected_cut_42579", "Selected cut at depth 12, code 338292, node 1163372",
                "At remaining fuel 9 and original index 1163372, selection on the full partial prefix of depth 12 and code 338292 returns the complete row with depth 12, base-four code 338292, original node 1163372, kind 2, reserved field 0, 1425 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42626", "selected_cut_42626", "Selected cut at depth 12, code 338444, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 338444 returns the complete row with depth 12, base-four code 338444, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84573-1163418", "unmarked_context_11_84573_1163418", "Unmarked parent at depth 11, code 84573",
                "The frontier Boolean is false at remaining fuel 10, original node 1163418, the whole prefixCache at depth 11 and code 84573, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84610-1164557", "unmarked_context_11_84610_1164557", "Unmarked parent at depth 11, code 84610",
                "The frontier Boolean is false at remaining fuel 10, original node 1164557, the whole prefixCache at depth 11 and code 84610, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84573-1163418", "node_context_11_84573_1163418", "Original split at fuel 10 and node 1163418",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1163372, 891951, 1163390, 1163417. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84610-1164557", "node_context_11_84610_1164557", "Original split at fuel 10 and node 1164557",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1164491, 893903, 1164556. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-338292-1163372", "context_12_338292_1163372", "Context at depth 12, code 338292, node 1163372",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338292 and original node 1163372, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-338444-448748", "context_12_338444_448748", "Context at depth 12, code 338444, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338444 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
