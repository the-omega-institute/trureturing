using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0224Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0224.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0224",
        H("Original frontier context coverage 0224"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10755", "selected_cut_10755", "Selected cut at depth 12, code 25227, node 290359",
                "At remaining fuel 9 and original index 290359, selection on the full partial prefix of depth 12 and code 25227 returns the complete row with depth 12, base-four code 25227, original node 290359, kind 2, reserved field 0, 2073 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10801", "selected_cut_10801", "Selected cut at depth 11, code 6319, node 291233",
                "At remaining fuel 10 and original index 291233, selection on the full partial prefix of depth 11 and code 6319 returns the complete row with depth 11, base-four code 6319, original node 291233, kind 2, reserved field 0, 3845 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6306-290360", "unmarked_context_11_6306_290360", "Unmarked parent at depth 11, code 6306",
                "The frontier Boolean is false at remaining fuel 10, original node 290360, the whole prefixCache at depth 11 and code 6306, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-394-291235", "unmarked_context_9_394_291235", "Unmarked parent at depth 9, code 394",
                "The frontier Boolean is false at remaining fuel 12, original node 291235, the whole prefixCache at depth 9 and code 394, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6306-290360", "node_context_11_6306_290360", "Original split at fuel 10 and node 290360",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 290278, 290306, 290332, 290359. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-394-291235", "node_context_9_394_291235", "Original split at fuel 12 and node 291235",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 290457, 290784, 291035, 291234. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25227-290359", "context_12_25227_290359", "Context at depth 12, code 25227, node 290359",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25227 and original node 290359, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-394-291235", "context_9_394_291235", "Context at depth 9, code 394, node 291235",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 394 and original node 291235, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1576_290457, context_10_1577_290784, context_10_1578_291035, context_10_1579_291234.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
