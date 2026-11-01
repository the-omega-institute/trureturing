using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0192Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0192.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0192",
        H("Original frontier context coverage 0192"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09219", "selected_cut_09219", "Selected cut at depth 13, code 93333, node 255288",
                "At remaining fuel 8 and original index 255288, selection on the full partial prefix of depth 13 and code 93333 returns the complete row with depth 13, base-four code 93333, original node 255288, kind 2, reserved field 0, 2313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09268", "selected_cut_09268", "Selected cut at depth 14, code 373495, node 256431",
                "At remaining fuel 7 and original index 256431, selection on the full partial prefix of depth 14 and code 373495 returns the complete row with depth 14, base-four code 373495, original node 256431, kind 2, reserved field 0, 905 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23333-255315", "unmarked_context_12_23333_255315", "Unmarked parent at depth 12, code 23333",
                "The frontier Boolean is false at remaining fuel 9, original node 255315, the whole prefixCache at depth 12 and code 23333, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23342-256328", "unmarked_context_12_23342_256328", "Unmarked parent at depth 12, code 23342",
                "The frontier Boolean is false at remaining fuel 9, original node 256328, the whole prefixCache at depth 12 and code 23342, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23333-255315", "node_context_12_23333_255315", "Original split at fuel 9 and node 255315",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 255254, 255288, 255306, 255314. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23342-256328", "node_context_12_23342_256328", "Original split at fuel 9 and node 256328",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 256261, 256304, 256320, 256327. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93333-255288", "context_13_93333_255288", "Context at depth 13, code 93333, node 255288",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93333 and original node 255288, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-373495-256431", "context_14_373495_256431", "Context at depth 14, code 373495, node 256431",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 373495 and original node 256431, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
