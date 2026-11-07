using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0250Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0250.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0250",
        H("Original frontier context coverage 0250"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12003", "selected_cut_12003", "Selected cut at depth 13, code 103692, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 103692 returns the complete row with depth 13, base-four code 103692, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12049", "selected_cut_12049", "Selected cut at depth 12, code 25936, node 320578",
                "At remaining fuel 9 and original index 320578, selection on the full partial prefix of depth 12 and code 25936 returns the complete row with depth 12, base-four code 25936, original node 320578, kind 2, reserved field 0, 3841 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25922-319769", "unmarked_context_12_25922_319769", "Unmarked parent at depth 12, code 25922",
                "The frontier Boolean is false at remaining fuel 9, original node 319769, the whole prefixCache at depth 12 and code 25922, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1620-320538", "unmarked_context_10_1620_320538", "Unmarked parent at depth 10, code 1620",
                "The frontier Boolean is false at remaining fuel 11, original node 320538, the whole prefixCache at depth 10 and code 1620, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25922-319769", "node_context_12_25922_319769", "Original split at fuel 9 and node 319769",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 319737, 319761, 319768. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1620-320538", "node_context_10_1620_320538", "Original split at fuel 11 and node 320538",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 319832, 319998, 320282, 320537. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25922-319769", "context_12_25922_319769", "Context at depth 12, code 25922, node 319769",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25922 and original node 319769, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_103688_3444, context_13_103689_319737, context_13_103690_319761, context_13_103691_319768.", DescribeRole.Theorem),
            Node("context-12-25936-320578", "context_12_25936_320578", "Context at depth 12, code 25936, node 320578",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25936 and original node 320578, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
