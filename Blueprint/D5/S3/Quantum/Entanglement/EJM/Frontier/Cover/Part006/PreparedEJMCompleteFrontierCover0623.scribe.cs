using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0623Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0623.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0623",
        H("Original frontier context coverage 0623"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29907", "selected_cut_29907", "Selected cut at depth 11, code 23472, node 754742",
                "At remaining fuel 10 and original index 754742, selection on the full partial prefix of depth 11 and code 23472 returns the complete row with depth 11, base-four code 23472, original node 754742, kind 2, reserved field 0, 3925 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29955", "selected_cut_29955", "Selected cut at depth 13, code 375882, node 756635",
                "At remaining fuel 8 and original index 756635, selection on the full partial prefix of depth 13 and code 375882 returns the complete row with depth 13, base-four code 375882, original node 756635, kind 2, reserved field 0, 1729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5868-754853", "unmarked_context_10_5868_754853", "Unmarked parent at depth 10, code 5868",
                "The frontier Boolean is false at remaining fuel 11, original node 754853, the whole prefixCache at depth 10 and code 5868, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93969-756522", "unmarked_context_12_93969_756522", "Unmarked parent at depth 12, code 93969",
                "The frontier Boolean is false at remaining fuel 9, original node 756522, the whole prefixCache at depth 12 and code 93969, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5868-754853", "node_context_10_5868_754853", "Original split at fuel 11 and node 754853",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 754742, 754775, 754814, 754852. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93969-756522", "node_context_12_93969_756522", "Original split at fuel 9 and node 756522",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 756454, 756486, 756512, 756521. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-23472-754742", "context_11_23472_754742", "Context at depth 11, code 23472, node 754742",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23472 and original node 754742, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-375882-756635", "context_13_375882_756635", "Context at depth 13, code 375882, node 756635",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375882 and original node 756635, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
