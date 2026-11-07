using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0325Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0325.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0325",
        H("Original frontier context coverage 0325"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15603", "selected_cut_15603", "Selected cut at depth 10, code 1743, node 399387",
                "At remaining fuel 11 and original index 399387, selection on the full partial prefix of depth 10 and code 1743 returns the complete row with depth 10, base-four code 1743, original node 399387, kind 2, reserved field 0, 1209 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15650", "selected_cut_15650", "Selected cut at depth 13, code 111656, node 400983",
                "At remaining fuel 8 and original index 400983, selection on the full partial prefix of depth 13 and code 111656 returns the complete row with depth 13, base-four code 111656, original node 400983, kind 2, reserved field 0, 3949 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-435-399388", "unmarked_context_9_435_399388", "Unmarked parent at depth 9, code 435",
                "The frontier Boolean is false at remaining fuel 12, original node 399388, the whole prefixCache at depth 9 and code 435, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27913-400906", "unmarked_context_12_27913_400906", "Unmarked parent at depth 12, code 27913",
                "The frontier Boolean is false at remaining fuel 9, original node 400906, the whole prefixCache at depth 12 and code 27913, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-435-399388", "node_context_9_435_399388", "Original split at fuel 12 and node 399388",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 399202, 399288, 399344, 399387. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27913-400906", "node_context_12_27913_400906", "Original split at fuel 9 and node 400906",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 400806, 400855, 400888, 400905. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1743-399387", "context_10_1743_399387", "Context at depth 10, code 1743, node 399387",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1743 and original node 399387, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111656-400983", "context_13_111656_400983", "Context at depth 13, code 111656, node 400983",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111656 and original node 400983, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
