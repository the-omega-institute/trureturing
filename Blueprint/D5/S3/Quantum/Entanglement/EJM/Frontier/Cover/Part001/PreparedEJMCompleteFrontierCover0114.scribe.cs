using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0114Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0114.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0114",
        H("Original frontier context coverage 0114"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05473", "selected_cut_05473", "Selected cut at depth 12, code 20545, node 169870",
                "At remaining fuel 9 and original index 169870, selection on the full partial prefix of depth 12 and code 20545 returns the complete row with depth 12, base-four code 20545, original node 169870, kind 2, reserved field 0, 3909 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05521", "selected_cut_05521", "Selected cut at depth 11, code 5143, node 1736",
                "At remaining fuel 10 and original index 1736, selection on the full partial prefix of depth 11 and code 5143 returns the complete row with depth 11, base-four code 5143, original node 1736, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-20546-169958", "unmarked_context_12_20546_169958", "Unmarked parent at depth 12, code 20546",
                "The frontier Boolean is false at remaining fuel 9, original node 169958, the whole prefixCache at depth 12 and code 20546, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5142-170815", "unmarked_context_11_5142_170815", "Unmarked parent at depth 11, code 5142",
                "The frontier Boolean is false at remaining fuel 10, original node 170815, the whole prefixCache at depth 11 and code 5142, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-20546-169958", "node_context_12_20546_169958", "Original split at fuel 9 and node 169958",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 169917, 169945, 169957. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5142-170815", "node_context_11_5142_170815", "Original split at fuel 10 and node 170815",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 170603, 170711, 170760, 170814. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-20545-169870", "context_12_20545_169870", "Context at depth 12, code 20545, node 169870",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20545 and original node 169870, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5143-1736", "context_11_5143_1736", "Context at depth 11, code 5143, node 1736",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5143 and original node 1736, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
