using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0660Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0660.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0660",
        H("Original frontier context coverage 0660"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31684", "selected_cut_31684", "Selected cut at depth 12, code 106099, node 812859",
                "At remaining fuel 9 and original index 812859, selection on the full partial prefix of depth 12 and code 106099 returns the complete row with depth 12, base-four code 106099, original node 812859, kind 2, reserved field 0, 3417 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31731", "selected_cut_31731", "Selected cut at depth 12, code 106146, node 769937",
                "At remaining fuel 9 and original index 769937, selection on the full partial prefix of depth 12 and code 106146 returns the complete row with depth 12, base-four code 106146, original node 769937, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26524-812860", "unmarked_context_11_26524_812860", "Unmarked parent at depth 11, code 26524",
                "The frontier Boolean is false at remaining fuel 10, original node 812860, the whole prefixCache at depth 11 and code 26524, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6633-814075", "unmarked_context_10_6633_814075", "Unmarked parent at depth 10, code 6633",
                "The frontier Boolean is false at remaining fuel 11, original node 814075, the whole prefixCache at depth 10 and code 6633, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26524-812860", "node_context_11_26524_812860", "Original split at fuel 10 and node 812860",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 812728, 812768, 812807, 812859. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6633-814075", "node_context_10_6633_814075", "Original split at fuel 11 and node 814075",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 813836, 813924, 814005, 814074. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-106099-812859", "context_12_106099_812859", "Context at depth 12, code 106099, node 812859",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 106099 and original node 812859, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-106146-769937", "context_12_106146_769937", "Context at depth 12, code 106146, node 769937",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 106146 and original node 769937, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
