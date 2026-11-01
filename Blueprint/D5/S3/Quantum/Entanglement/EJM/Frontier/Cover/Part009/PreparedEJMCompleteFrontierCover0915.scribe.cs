using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0915Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0915.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0915",
        H("Original frontier context coverage 0915"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43923", "selected_cut_43923", "Selected cut at depth 12, code 352824, node 1205108",
                "At remaining fuel 9 and original index 1205108, selection on the full partial prefix of depth 12 and code 352824 returns the complete row with depth 12, base-four code 352824, original node 1205108, kind 2, reserved field 0, 2581 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43970", "selected_cut_43970", "Selected cut at depth 11, code 88232, node 1206453",
                "At remaining fuel 10 and original index 1206453, selection on the full partial prefix of depth 11 and code 88232 returns the complete row with depth 11, base-four code 88232, original node 1206453, kind 2, reserved field 0, 1705 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88206-1205202", "unmarked_context_11_88206_1205202", "Unmarked parent at depth 11, code 88206",
                "The frontier Boolean is false at remaining fuel 10, original node 1205202, the whole prefixCache at depth 11 and code 88206, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22057-1206422", "unmarked_context_10_22057_1206422", "Unmarked parent at depth 10, code 22057",
                "The frontier Boolean is false at remaining fuel 11, original node 1206422, the whole prefixCache at depth 10 and code 22057, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88206-1205202", "node_context_11_88206_1205202", "Original split at fuel 10 and node 1205202",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1205108, 1205148, 893903, 1205201. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22057-1206422", "node_context_10_22057_1206422", "Original split at fuel 11 and node 1206422",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1206221, 1206269, 1206328, 1206421. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-352824-1205108", "context_12_352824_1205108", "Context at depth 12, code 352824, node 1205108",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352824 and original node 1205108, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88232-1206453", "context_11_88232_1206453", "Context at depth 11, code 88232, node 1206453",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88232 and original node 1206453, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
