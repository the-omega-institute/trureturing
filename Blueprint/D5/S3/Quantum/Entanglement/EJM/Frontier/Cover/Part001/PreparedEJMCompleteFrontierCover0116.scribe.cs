using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0116Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0116.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0116",
        H("Original frontier context coverage 0116"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05570", "selected_cut_05570", "Selected cut at depth 12, code 20627, node 172199",
                "At remaining fuel 9 and original index 172199, selection on the full partial prefix of depth 12 and code 20627 returns the complete row with depth 12, base-four code 20627, original node 172199, kind 2, reserved field 0, 1881 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05618", "selected_cut_05618", "Selected cut at depth 13, code 82991, node 173615",
                "At remaining fuel 8 and original index 173615, selection on the full partial prefix of depth 13 and code 82991 returns the complete row with depth 13, base-four code 82991, original node 173615, kind 2, reserved field 0, 1181 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5156-172200", "unmarked_context_11_5156_172200", "Unmarked parent at depth 11, code 5156",
                "The frontier Boolean is false at remaining fuel 10, original node 172200, the whole prefixCache at depth 11 and code 5156, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-20746-173486", "unmarked_context_12_20746_173486", "Unmarked parent at depth 12, code 20746",
                "The frontier Boolean is false at remaining fuel 9, original node 173486, the whole prefixCache at depth 12 and code 20746, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5156-172200", "node_context_11_5156_172200", "Original split at fuel 10 and node 172200",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 172121, 172153, 172174, 172199. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-20746-173486", "node_context_12_20746_173486", "Original split at fuel 9 and node 173486",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 173413, 173459, 173478, 173485. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-20627-172199", "context_12_20627_172199", "Context at depth 12, code 20627, node 172199",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20627 and original node 172199, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-82991-173615", "context_13_82991_173615", "Context at depth 13, code 82991, node 173615",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 82991 and original node 173615, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
