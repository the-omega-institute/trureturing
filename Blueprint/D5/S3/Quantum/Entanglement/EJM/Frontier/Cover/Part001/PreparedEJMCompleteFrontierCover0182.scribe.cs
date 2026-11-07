using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0182Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0182.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0182",
        H("Original frontier context coverage 0182"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08740", "selected_cut_08740", "Selected cut at depth 13, code 92413, node 243953",
                "At remaining fuel 8 and original index 243953, selection on the full partial prefix of depth 13 and code 92413 returns the complete row with depth 13, base-four code 92413, original node 243953, kind 2, reserved field 0, 2945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08786", "selected_cut_08786", "Selected cut at depth 13, code 92453, node 244918",
                "At remaining fuel 8 and original index 244918, selection on the full partial prefix of depth 13 and code 92453 returns the complete row with depth 13, base-four code 92453, original node 244918, kind 2, reserved field 0, 3633 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23103-243986", "unmarked_context_12_23103_243986", "Unmarked parent at depth 12, code 23103",
                "The frontier Boolean is false at remaining fuel 9, original node 243986, the whole prefixCache at depth 12 and code 23103, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23112-244864", "unmarked_context_12_23112_244864", "Unmarked parent at depth 12, code 23112",
                "The frontier Boolean is false at remaining fuel 9, original node 244864, the whole prefixCache at depth 12 and code 23112, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23103-243986", "node_context_12_23103_243986", "Original split at fuel 9 and node 243986",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 243912, 243953, 243978, 243985. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23112-244864", "node_context_12_23112_244864", "Original split at fuel 9 and node 244864",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 244832, 244853, 244863. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-92413-243953", "context_13_92413_243953", "Context at depth 13, code 92413, node 243953",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92413 and original node 243953, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-92453-244918", "context_13_92453_244918", "Context at depth 13, code 92453, node 244918",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92453 and original node 244918, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
