using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0443Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0443.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0443",
        H("Original frontier context coverage 0443"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21267", "selected_cut_21267", "Selected cut at depth 12, code 74895, node 544318",
                "At remaining fuel 9 and original index 544318, selection on the full partial prefix of depth 12 and code 74895 returns the complete row with depth 12, base-four code 74895, original node 544318, kind 2, reserved field 0, 1849 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21313", "selected_cut_21313", "Selected cut at depth 11, code 18736, node 545276",
                "At remaining fuel 10 and original index 545276, selection on the full partial prefix of depth 11 and code 18736 returns the complete row with depth 11, base-four code 18736, original node 545276, kind 2, reserved field 0, 2005 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18723-544319", "unmarked_context_11_18723_544319", "Unmarked parent at depth 11, code 18723",
                "The frontier Boolean is false at remaining fuel 10, original node 544319, the whole prefixCache at depth 11 and code 18723, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1170-545251", "unmarked_context_9_1170_545251", "Unmarked parent at depth 9, code 1170",
                "The frontier Boolean is false at remaining fuel 12, original node 545251, the whole prefixCache at depth 9 and code 1170, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18723-544319", "node_context_11_18723_544319", "Original split at fuel 10 and node 544319",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 544258, 544275, 544300, 544318. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1170-545251", "node_context_9_1170_545251", "Original split at fuel 12 and node 545251",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 544320, 544741, 544989, 545250. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-74895-544318", "context_12_74895_544318", "Context at depth 12, code 74895, node 544318",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74895 and original node 544318, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-18736-545276", "context_11_18736_545276", "Context at depth 11, code 18736, node 545276",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18736 and original node 545276, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
