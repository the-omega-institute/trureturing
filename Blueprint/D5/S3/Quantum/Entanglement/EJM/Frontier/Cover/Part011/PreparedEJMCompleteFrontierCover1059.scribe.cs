using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1059Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1059.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1059",
        H("Original frontier context coverage 1059"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50835", "selected_cut_50835", "Selected cut at depth 12, code 441360, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 441360 returns the complete row with depth 12, base-four code 441360, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50883", "selected_cut_50883", "Selected cut at depth 11, code 110424, node 1458943",
                "At remaining fuel 10 and original index 1458943, selection on the full partial prefix of depth 11 and code 110424 returns the complete row with depth 11, base-four code 110424, original node 1458943, kind 2, reserved field 0, 1469 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-110340-1456670", "unmarked_context_11_110340_1456670", "Unmarked parent at depth 11, code 110340",
                "The frontier Boolean is false at remaining fuel 10, original node 1456670, the whole prefixCache at depth 11 and code 110340, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6900-1458893", "unmarked_context_9_6900_1458893", "Unmarked parent at depth 9, code 6900",
                "The frontier Boolean is false at remaining fuel 12, original node 1458893, the whole prefixCache at depth 9 and code 6900, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-110340-1456670", "node_context_11_110340_1456670", "Original split at fuel 10 and node 1456670",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1456565, 1456619, 1456669. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6900-1458893", "node_context_9_6900_1458893", "Original split at fuel 12 and node 1458893",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1458072, 1458373, 1458665, 1458892. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-441360-435790", "context_12_441360_435790", "Context at depth 12, code 441360, node 435790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 441360 and original node 435790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-110424-1458943", "context_11_110424_1458943", "Context at depth 11, code 110424, node 1458943",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 110424 and original node 1458943, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
