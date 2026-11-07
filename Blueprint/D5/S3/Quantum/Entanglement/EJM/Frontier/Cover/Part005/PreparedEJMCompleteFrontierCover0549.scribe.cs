using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0549Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0549.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0549",
        H("Original frontier context coverage 0549"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26356", "selected_cut_26356", "Selected cut at depth 12, code 88768, node 666346",
                "At remaining fuel 9 and original index 666346, selection on the full partial prefix of depth 12 and code 88768 returns the complete row with depth 12, base-four code 88768, original node 666346, kind 2, reserved field 0, 1029 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26403", "selected_cut_26403", "Selected cut at depth 13, code 355383, node 667935",
                "At remaining fuel 8 and original index 667935, selection on the full partial prefix of depth 13 and code 355383 returns the complete row with depth 13, base-four code 355383, original node 667935, kind 2, reserved field 0, 845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5547-666334", "unmarked_context_10_5547_666334", "Unmarked parent at depth 10, code 5547",
                "The frontier Boolean is false at remaining fuel 11, original node 666334, the whole prefixCache at depth 10 and code 5547, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22210-667797", "unmarked_context_11_22210_667797", "Unmarked parent at depth 11, code 22210",
                "The frontier Boolean is false at remaining fuel 10, original node 667797, the whole prefixCache at depth 11 and code 22210, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5547-666334", "node_context_10_5547_666334", "Original split at fuel 11 and node 666334",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 666210, 666255, 666289, 666333. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22210-667797", "node_context_11_22210_667797", "Original split at fuel 10 and node 667797",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 667458, 667635, 667796. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-5547-666334", "context_10_5547_666334", "Context at depth 10, code 5547, node 666334",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 5547 and original node 666334, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_22188_666210, context_11_22189_666255, context_11_22190_666289, context_11_22191_666333.", DescribeRole.Theorem),
            Node("context-13-355383-667935", "context_13_355383_667935", "Context at depth 13, code 355383, node 667935",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355383 and original node 667935, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
