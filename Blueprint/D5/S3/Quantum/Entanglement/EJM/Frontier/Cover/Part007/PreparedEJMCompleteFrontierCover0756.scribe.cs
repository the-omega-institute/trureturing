using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0756Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0756.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0756",
        H("Original frontier context coverage 0756"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36291", "selected_cut_36291", "Selected cut at depth 11, code 72114, node 959787",
                "At remaining fuel 10 and original index 959787, selection on the full partial prefix of depth 11 and code 72114 returns the complete row with depth 11, base-four code 72114, original node 959787, kind 2, reserved field 0, 1797 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36339", "selected_cut_36339", "Selected cut at depth 12, code 288555, node 961928",
                "At remaining fuel 9 and original index 961928, selection on the full partial prefix of depth 12 and code 288555 returns the complete row with depth 12, base-four code 288555, original node 961928, kind 2, reserved field 0, 3321 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18028-959826", "unmarked_context_10_18028_959826", "Unmarked parent at depth 10, code 18028",
                "The frontier Boolean is false at remaining fuel 11, original node 959826, the whole prefixCache at depth 10 and code 18028, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72137-961732", "unmarked_context_11_72137_961732", "Unmarked parent at depth 11, code 72137",
                "The frontier Boolean is false at remaining fuel 10, original node 961732, the whole prefixCache at depth 11 and code 72137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18028-959826", "node_context_10_18028_959826", "Original split at fuel 11 and node 959826",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 959721, 959759, 959787, 959825. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72137-961732", "node_context_11_72137_961732", "Original split at fuel 10 and node 961732",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 961600, 961639, 961685, 961731. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-72114-959787", "context_11_72114_959787", "Context at depth 11, code 72114, node 959787",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72114 and original node 959787, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-288555-961928", "context_12_288555_961928", "Context at depth 12, code 288555, node 961928",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288555 and original node 961928, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
