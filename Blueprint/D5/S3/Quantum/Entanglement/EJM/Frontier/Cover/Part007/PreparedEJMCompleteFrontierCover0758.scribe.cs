using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0758Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0758.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0758",
        H("Original frontier context coverage 0758"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36388", "selected_cut_36388", "Selected cut at depth 12, code 288619, node 963784",
                "At remaining fuel 9 and original index 963784, selection on the full partial prefix of depth 12 and code 288619 returns the complete row with depth 12, base-four code 288619, original node 963784, kind 2, reserved field 0, 2045 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36435", "selected_cut_36435", "Selected cut at depth 11, code 72174, node 965194",
                "At remaining fuel 10 and original index 965194, selection on the full partial prefix of depth 11 and code 72174 returns the complete row with depth 11, base-four code 72174, original node 965194, kind 2, reserved field 0, 3345 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72154-963785", "unmarked_context_11_72154_963785", "Unmarked parent at depth 11, code 72154",
                "The frontier Boolean is false at remaining fuel 10, original node 963785, the whole prefixCache at depth 11 and code 72154, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72172-965082", "unmarked_context_11_72172_965082", "Unmarked parent at depth 11, code 72172",
                "The frontier Boolean is false at remaining fuel 10, original node 965082, the whole prefixCache at depth 11 and code 72172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72154-963785", "node_context_11_72154_963785", "Original split at fuel 10 and node 963785",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 963715, 896706, 963745, 963784. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72172-965082", "node_context_11_72172_965082", "Original split at fuel 10 and node 965082",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 965007, 965027, 965061, 965081. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-288619-963784", "context_12_288619_963784", "Context at depth 12, code 288619, node 963784",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288619 and original node 963784, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-72174-965194", "context_11_72174_965194", "Context at depth 11, code 72174, node 965194",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72174 and original node 965194, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
