using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0747Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0747.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0747",
        H("Original frontier context coverage 0747"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35859", "selected_cut_35859", "Selected cut at depth 11, code 71862, node 944446",
                "At remaining fuel 10 and original index 944446, selection on the full partial prefix of depth 11 and code 71862 returns the complete row with depth 11, base-four code 71862, original node 944446, kind 2, reserved field 0, 1081 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35906", "selected_cut_35906", "Selected cut at depth 12, code 287516, node 946046",
                "At remaining fuel 9 and original index 946046, selection on the full partial prefix of depth 12 and code 287516 returns the complete row with depth 12, base-four code 287516, original node 946046, kind 2, reserved field 0, 3721 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17965-944467", "unmarked_context_10_17965_944467", "Unmarked parent at depth 10, code 17965",
                "The frontier Boolean is false at remaining fuel 11, original node 944467, the whole prefixCache at depth 10 and code 17965, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71878-945986", "unmarked_context_11_71878_945986", "Unmarked parent at depth 11, code 71878",
                "The frontier Boolean is false at remaining fuel 10, original node 945986, the whole prefixCache at depth 11 and code 71878, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17965-944467", "node_context_10_17965_944467", "Original split at fuel 11 and node 944467",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 944419, 944434, 944446, 944466. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71878-945986", "node_context_11_71878_945986", "Original split at fuel 10 and node 945986",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 945782, 945855, 945915, 945985. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-71862-944446", "context_11_71862_944446", "Context at depth 11, code 71862, node 944446",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71862 and original node 944446, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-287516-946046", "context_12_287516_946046", "Context at depth 12, code 287516, node 946046",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287516 and original node 946046, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
