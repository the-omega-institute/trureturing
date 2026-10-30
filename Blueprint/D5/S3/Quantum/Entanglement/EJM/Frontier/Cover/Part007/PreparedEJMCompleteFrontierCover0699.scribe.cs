using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0699Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0699.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0699",
        H("Original frontier context coverage 0699"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33556", "selected_cut_33556", "Selected cut at depth 13, code 441472, node 864119",
                "At remaining fuel 8 and original index 864119, selection on the full partial prefix of depth 13 and code 441472 returns the complete row with depth 13, base-four code 441472, original node 864119, kind 2, reserved field 0, 1737 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33603", "selected_cut_33603", "Selected cut at depth 13, code 441519, node 865385",
                "At remaining fuel 8 and original index 865385, selection on the full partial prefix of depth 13 and code 441519 returns the complete row with depth 13, base-four code 441519, original node 865385, kind 2, reserved field 0, 521 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-6897-864091", "unmarked_context_10_6897_864091", "Unmarked parent at depth 10, code 6897",
                "The frontier Boolean is false at remaining fuel 11, original node 864091, the whole prefixCache at depth 10 and code 6897, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27594-865387", "unmarked_context_11_27594_865387", "Unmarked parent at depth 11, code 27594",
                "The frontier Boolean is false at remaining fuel 10, original node 865387, the whole prefixCache at depth 11 and code 27594, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-6897-864091", "node_context_10_6897_864091", "Original split at fuel 11 and node 864091",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 862778, 863285, 863807, 864090. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27594-865387", "node_context_11_27594_865387", "Original split at fuel 10 and node 865387",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 865105, 865213, 865292, 865386. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-6897-864091", "context_10_6897_864091", "Context at depth 10, code 6897, node 864091",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 6897 and original node 864091, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_27588_862778, context_11_27589_863285, context_11_27590_863807, context_11_27591_864090.", DescribeRole.Theorem),
            Node("context-11-27594-865387", "context_11_27594_865387", "Context at depth 11, code 27594, node 865387",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27594 and original node 865387, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_110376_865105, context_12_110377_865213, context_12_110378_865292, context_12_110379_865386.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
