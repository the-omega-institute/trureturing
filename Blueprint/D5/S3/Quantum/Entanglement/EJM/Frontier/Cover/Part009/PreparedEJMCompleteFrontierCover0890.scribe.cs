using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0890Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0890.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0890",
        H("Original frontier context coverage 0890"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42724", "selected_cut_42724", "Selected cut at depth 12, code 338575, node 1167213",
                "At remaining fuel 9 and original index 1167213, selection on the full partial prefix of depth 12 and code 338575 returns the complete row with depth 12, base-four code 338575, original node 1167213, kind 2, reserved field 0, 993 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42771", "selected_cut_42771", "Selected cut at depth 12, code 338715, node 1168536",
                "At remaining fuel 9 and original index 1168536, selection on the full partial prefix of depth 12 and code 338715 returns the complete row with depth 12, base-four code 338715, original node 1168536, kind 2, reserved field 0, 2945 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84643-1167214", "unmarked_context_11_84643_1167214", "Unmarked parent at depth 11, code 84643",
                "The frontier Boolean is false at remaining fuel 10, original node 1167214, the whole prefixCache at depth 11 and code 84643, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84677-1168393", "unmarked_context_11_84677_1168393", "Unmarked parent at depth 11, code 84677",
                "The frontier Boolean is false at remaining fuel 10, original node 1168393, the whole prefixCache at depth 11 and code 84677, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84643-1167214", "node_context_11_84643_1167214", "Original split at fuel 10 and node 1167214",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1167167, 1167185, 1167200, 1167213. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84677-1168393", "node_context_11_84677_1168393", "Original split at fuel 10 and node 1168393",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1118965, 1168327, 1168392. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-338575-1167213", "context_12_338575_1167213", "Context at depth 12, code 338575, node 1167213",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338575 and original node 1167213, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-338715-1168536", "context_12_338715_1168536", "Context at depth 12, code 338715, node 1168536",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338715 and original node 1168536, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
