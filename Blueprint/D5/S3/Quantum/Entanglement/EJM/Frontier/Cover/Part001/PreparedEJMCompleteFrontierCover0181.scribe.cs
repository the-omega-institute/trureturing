using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0181Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0181.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0181",
        H("Original frontier context coverage 0181"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08692", "selected_cut_08692", "Selected cut at depth 13, code 92368, node 242947",
                "At remaining fuel 8 and original index 242947, selection on the full partial prefix of depth 13 and code 92368 returns the complete row with depth 13, base-four code 92368, original node 242947, kind 2, reserved field 0, 645 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08739", "selected_cut_08739", "Selected cut at depth 13, code 92412, node 243912",
                "At remaining fuel 8 and original index 243912, selection on the full partial prefix of depth 13 and code 92412 returns the complete row with depth 13, base-four code 92412, original node 243912, kind 2, reserved field 0, 81 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23091-242934", "unmarked_context_12_23091_242934", "Unmarked parent at depth 12, code 23091",
                "The frontier Boolean is false at remaining fuel 9, original node 242934, the whole prefixCache at depth 12 and code 23091, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23102-243907", "unmarked_context_12_23102_243907", "Unmarked parent at depth 12, code 23102",
                "The frontier Boolean is false at remaining fuel 9, original node 243907, the whole prefixCache at depth 12 and code 23102, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23091-242934", "node_context_12_23091_242934", "Original split at fuel 9 and node 242934",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 242852, 242904, 242925, 242933. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23102-243907", "node_context_12_23102_243907", "Original split at fuel 9 and node 243907",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 243827, 243876, 243899, 243906. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-23091-242934", "context_12_23091_242934", "Context at depth 12, code 23091, node 242934",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23091 and original node 242934, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_92364_242852, context_13_92365_242904, context_13_92366_242925, context_13_92367_242933.", DescribeRole.Theorem),
            Node("context-13-92412-243912", "context_13_92412_243912", "Context at depth 13, code 92412, node 243912",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92412 and original node 243912, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
