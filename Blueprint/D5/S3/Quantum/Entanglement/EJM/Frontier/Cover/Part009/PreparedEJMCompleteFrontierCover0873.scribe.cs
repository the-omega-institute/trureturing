using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0873Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0873.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0873",
        H("Original frontier context coverage 0873"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41906", "selected_cut_41906", "Selected cut at depth 12, code 336929, node 1145618",
                "At remaining fuel 9 and original index 1145618, selection on the full partial prefix of depth 12 and code 336929 returns the complete row with depth 12, base-four code 336929, original node 1145618, kind 2, reserved field 0, 2309 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41953", "selected_cut_41953", "Selected cut at depth 10, code 21061, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 21061 returns the complete row with depth 10, base-four code 21061, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84232-1145711", "unmarked_context_11_84232_1145711", "Unmarked parent at depth 11, code 84232",
                "The frontier Boolean is false at remaining fuel 10, original node 1145711, the whole prefixCache at depth 11 and code 84232, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21060-1146992", "unmarked_context_10_21060_1146992", "Unmarked parent at depth 10, code 21060",
                "The frontier Boolean is false at remaining fuel 11, original node 1146992, the whole prefixCache at depth 10 and code 21060, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84232-1145711", "node_context_11_84232_1145711", "Original split at fuel 10 and node 1145711",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1145618, 1145665, 1145710. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21060-1146992", "node_context_10_21060_1146992", "Original split at fuel 11 and node 1146992",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1146651, 1146736, 1146875, 1146991. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336929-1145618", "context_12_336929_1145618", "Context at depth 12, code 336929, node 1145618",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336929 and original node 1145618, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-21061-893098", "context_10_21061_893098", "Context at depth 10, code 21061, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21061 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
