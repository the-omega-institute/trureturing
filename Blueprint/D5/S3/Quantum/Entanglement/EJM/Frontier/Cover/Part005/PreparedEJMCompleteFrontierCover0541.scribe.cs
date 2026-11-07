using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0541Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0541.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0541",
        H("Original frontier context coverage 0541"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25971", "selected_cut_25971", "Selected cut at depth 12, code 88221, node 657228",
                "At remaining fuel 9 and original index 657228, selection on the full partial prefix of depth 12 and code 88221 returns the complete row with depth 12, base-four code 88221, original node 657228, kind 2, reserved field 0, 2097 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26018", "selected_cut_26018", "Selected cut at depth 13, code 354326, node 658224",
                "At remaining fuel 8 and original index 658224, selection on the full partial prefix of depth 13 and code 354326 returns the complete row with depth 13, base-four code 354326, original node 658224, kind 2, reserved field 0, 1413 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22055-657272", "unmarked_context_11_22055_657272", "Unmarked parent at depth 11, code 22055",
                "The frontier Boolean is false at remaining fuel 10, original node 657272, the whole prefixCache at depth 11 and code 22055, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-344-657998", "unmarked_context_8_344_657998", "Unmarked parent at depth 8, code 344",
                "The frontier Boolean is false at remaining fuel 13, original node 657998, the whole prefixCache at depth 8 and code 344, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22055-657272", "node_context_11_22055_657272", "Original split at fuel 10 and node 657272",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 657212, 657228, 657251, 657271. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-344-657998", "node_context_8_344_657998", "Original split at fuel 13 and node 657998",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 653883, 656526, 657664, 657997. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-88221-657228", "context_12_88221_657228", "Context at depth 12, code 88221, node 657228",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88221 and original node 657228, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-354326-658224", "context_13_354326_658224", "Context at depth 13, code 354326, node 658224",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354326 and original node 658224, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
