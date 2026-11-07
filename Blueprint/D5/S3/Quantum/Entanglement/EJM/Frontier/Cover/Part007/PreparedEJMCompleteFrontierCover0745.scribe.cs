using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0745Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0745.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0745",
        H("Original frontier context coverage 0745"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35763", "selected_cut_35763", "Selected cut at depth 12, code 287286, node 942214",
                "At remaining fuel 9 and original index 942214, selection on the full partial prefix of depth 12 and code 287286 returns the complete row with depth 12, base-four code 287286, original node 942214, kind 2, reserved field 0, 2333 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35811", "selected_cut_35811", "Selected cut at depth 12, code 287358, node 943431",
                "At remaining fuel 9 and original index 943431, selection on the full partial prefix of depth 12 and code 287358 returns the complete row with depth 12, base-four code 287358, original node 943431, kind 2, reserved field 0, 1469 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71821-942262", "unmarked_context_11_71821_942262", "Unmarked parent at depth 11, code 71821",
                "The frontier Boolean is false at remaining fuel 10, original node 942262, the whole prefixCache at depth 11 and code 71821, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71837-943334", "unmarked_context_11_71837_943334", "Unmarked parent at depth 11, code 71837",
                "The frontier Boolean is false at remaining fuel 10, original node 943334, the whole prefixCache at depth 11 and code 71837, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71821-942262", "node_context_11_71821_942262", "Original split at fuel 10 and node 942262",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 942139, 942182, 942214, 942261. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71837-943334", "node_context_11_71837_943334", "Original split at fuel 10 and node 943334",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 943284, 896706, 943301, 943333. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-287286-942214", "context_12_287286_942214", "Context at depth 12, code 287286, node 942214",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287286 and original node 942214, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-287358-943431", "context_12_287358_943431", "Context at depth 12, code 287358, node 943431",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287358 and original node 943431, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
