using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0772Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0772.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0772",
        H("Original frontier context coverage 0772"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37058", "selected_cut_37058", "Selected cut at depth 12, code 299270, node 989211",
                "At remaining fuel 9 and original index 989211, selection on the full partial prefix of depth 12 and code 299270 returns the complete row with depth 12, base-four code 299270, original node 989211, kind 2, reserved field 0, 3845 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37106", "selected_cut_37106", "Selected cut at depth 12, code 299315, node 991321",
                "At remaining fuel 9 and original index 991321, selection on the full partial prefix of depth 12 and code 299315 returns the complete row with depth 12, base-four code 299315, original node 991321, kind 2, reserved field 0, 2405 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74817-989283", "unmarked_context_11_74817_989283", "Unmarked parent at depth 11, code 74817",
                "The frontier Boolean is false at remaining fuel 10, original node 989283, the whole prefixCache at depth 11 and code 74817, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18706-991168", "unmarked_context_10_18706_991168", "Unmarked parent at depth 10, code 18706",
                "The frontier Boolean is false at remaining fuel 11, original node 991168, the whole prefixCache at depth 10 and code 18706, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74817-989283", "node_context_11_74817_989283", "Original split at fuel 10 and node 989283",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 989139, 891951, 989211, 989282. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18706-991168", "node_context_10_18706_991168", "Original split at fuel 11 and node 991168",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 990632, 990812, 990982, 991167. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-299270-989211", "context_12_299270_989211", "Context at depth 12, code 299270, node 989211",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299270 and original node 989211, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-299315-991321", "context_12_299315_991321", "Context at depth 12, code 299315, node 991321",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299315 and original node 991321, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
