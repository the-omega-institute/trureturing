using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0970Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0970.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0970",
        H("Original frontier context coverage 0970"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46564", "selected_cut_46564", "Selected cut at depth 12, code 370990, node 1298697",
                "At remaining fuel 9 and original index 1298697, selection on the full partial prefix of depth 12 and code 370990 returns the complete row with depth 12, base-four code 370990, original node 1298697, kind 2, reserved field 0, 1889 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46611", "selected_cut_46611", "Selected cut at depth 11, code 92775, node 1300155",
                "At remaining fuel 10 and original index 1300155, selection on the full partial prefix of depth 11 and code 92775 returns the complete row with depth 11, base-four code 92775, original node 1300155, kind 2, reserved field 0, 1465 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92747-1298728", "unmarked_context_11_92747_1298728", "Unmarked parent at depth 11, code 92747",
                "The frontier Boolean is false at remaining fuel 10, original node 1298728, the whole prefixCache at depth 11 and code 92747, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23192-1300031", "unmarked_context_10_23192_1300031", "Unmarked parent at depth 10, code 23192",
                "The frontier Boolean is false at remaining fuel 11, original node 1300031, the whole prefixCache at depth 10 and code 23192, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92747-1298728", "node_context_11_92747_1298728", "Original split at fuel 10 and node 1298728",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1298637, 1298669, 1298697, 1298727. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23192-1300031", "node_context_10_23192_1300031", "Original split at fuel 11 and node 1300031",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1299880, 1299921, 1299986, 1300030. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-370990-1298697", "context_12_370990_1298697", "Context at depth 12, code 370990, node 1298697",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370990 and original node 1298697, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-92775-1300155", "context_11_92775_1300155", "Context at depth 11, code 92775, node 1300155",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92775 and original node 1300155, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
