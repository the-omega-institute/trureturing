using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0102Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0102.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0102",
        H("Original frontier context coverage 0102"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04898", "selected_cut_04898", "Selected cut at depth 12, code 18773, node 126371",
                "At remaining fuel 9 and original index 126371, selection on the full partial prefix of depth 12 and code 18773 returns the complete row with depth 12, base-four code 18773, original node 126371, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04946", "selected_cut_04946", "Selected cut at depth 13, code 75143, node 155258",
                "At remaining fuel 8 and original index 155258, selection on the full partial prefix of depth 13 and code 75143 returns the complete row with depth 13, base-four code 75143, original node 155258, kind 2, reserved field 0, 1109 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18774-154629", "unmarked_context_12_18774_154629", "Unmarked parent at depth 12, code 18774",
                "The frontier Boolean is false at remaining fuel 9, original node 154629, the whole prefixCache at depth 12 and code 18774, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18784-155211", "unmarked_context_12_18784_155211", "Unmarked parent at depth 12, code 18784",
                "The frontier Boolean is false at remaining fuel 9, original node 155211, the whole prefixCache at depth 12 and code 18784, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18774-154629", "node_context_12_18774_154629", "Original split at fuel 9 and node 154629",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 154597, 154617, 154628. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18784-155211", "node_context_12_18784_155211", "Original split at fuel 9 and node 155211",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 155179, 155200, 155210. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18773-126371", "context_12_18773_126371", "Context at depth 12, code 18773, node 126371",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18773 and original node 126371, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-75143-155258", "context_13_75143_155258", "Context at depth 13, code 75143, node 155258",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 75143 and original node 155258, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
