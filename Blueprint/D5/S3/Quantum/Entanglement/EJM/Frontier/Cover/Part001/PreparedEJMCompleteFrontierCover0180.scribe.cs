using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0180Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0180.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0180",
        H("Original frontier context coverage 0180"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08644", "selected_cut_08644", "Selected cut at depth 13, code 92320, node 241926",
                "At remaining fuel 8 and original index 241926, selection on the full partial prefix of depth 13 and code 92320 returns the complete row with depth 13, base-four code 92320, original node 241926, kind 2, reserved field 0, 1281 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08691", "selected_cut_08691", "Selected cut at depth 13, code 92367, node 242933",
                "At remaining fuel 8 and original index 242933, selection on the full partial prefix of depth 13 and code 92367 returns the complete row with depth 13, base-four code 92367, original node 242933, kind 2, reserved field 0, 1013 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23079-241909", "unmarked_context_12_23079_241909", "Unmarked parent at depth 12, code 23079",
                "The frontier Boolean is false at remaining fuel 9, original node 241909, the whole prefixCache at depth 12 and code 23079, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23090-242831", "unmarked_context_12_23090_242831", "Unmarked parent at depth 12, code 23090",
                "The frontier Boolean is false at remaining fuel 9, original node 242831, the whole prefixCache at depth 12 and code 23090, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23079-241909", "node_context_12_23079_241909", "Original split at fuel 9 and node 241909",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 241834, 241879, 241900, 241908. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23090-242831", "node_context_12_23090_242831", "Original split at fuel 9 and node 242831",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 242764, 242804, 242822, 242830. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-23079-241909", "context_12_23079_241909", "Context at depth 12, code 23079, node 241909",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23079 and original node 241909, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_92316_241834, context_13_92317_241879, context_13_92318_241900, context_13_92319_241908.", DescribeRole.Theorem),
            Node("context-13-92367-242933", "context_13_92367_242933", "Context at depth 13, code 92367, node 242933",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92367 and original node 242933, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
