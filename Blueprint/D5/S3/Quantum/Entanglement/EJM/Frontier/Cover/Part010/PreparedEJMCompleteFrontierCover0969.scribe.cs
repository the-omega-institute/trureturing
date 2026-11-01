using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0969Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0969.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0969",
        H("Original frontier context coverage 0969"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46516", "selected_cut_46516", "Selected cut at depth 11, code 92719, node 1297262",
                "At remaining fuel 10 and original index 1297262, selection on the full partial prefix of depth 11 and code 92719 returns the complete row with depth 11, base-four code 92719, original node 1297262, kind 2, reserved field 0, 1005 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46563", "selected_cut_46563", "Selected cut at depth 12, code 370989, node 1298669",
                "At remaining fuel 9 and original index 1298669, selection on the full partial prefix of depth 12 and code 370989 returns the complete row with depth 12, base-four code 370989, original node 1298669, kind 2, reserved field 0, 2213 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23179-1297263", "unmarked_context_10_23179_1297263", "Unmarked parent at depth 10, code 23179",
                "The frontier Boolean is false at remaining fuel 11, original node 1297263, the whole prefixCache at depth 10 and code 23179, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92745-1298609", "unmarked_context_11_92745_1298609", "Unmarked parent at depth 11, code 92745",
                "The frontier Boolean is false at remaining fuel 10, original node 1298609, the whole prefixCache at depth 11 and code 92745, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23179-1297263", "node_context_10_23179_1297263", "Original split at fuel 11 and node 1297263",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1297191, 1297225, 1297247, 1297262. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92745-1298609", "node_context_11_92745_1298609", "Original split at fuel 10 and node 1298609",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1298546, 891951, 1298577, 1298608. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92719-1297262", "context_11_92719_1297262", "Context at depth 11, code 92719, node 1297262",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92719 and original node 1297262, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-370989-1298669", "context_12_370989_1298669", "Context at depth 12, code 370989, node 1298669",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370989 and original node 1298669, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
