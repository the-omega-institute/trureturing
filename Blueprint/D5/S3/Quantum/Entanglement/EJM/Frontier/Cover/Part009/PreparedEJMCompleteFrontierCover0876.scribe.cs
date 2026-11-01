using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0876Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0876.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0876",
        H("Original frontier context coverage 0876"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42051", "selected_cut_42051", "Selected cut at depth 12, code 337197, node 1149592",
                "At remaining fuel 9 and original index 1149592, selection on the full partial prefix of depth 12 and code 337197 returns the complete row with depth 12, base-four code 337197, original node 1149592, kind 2, reserved field 0, 2061 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42099", "selected_cut_42099", "Selected cut at depth 12, code 337275, node 1150751",
                "At remaining fuel 9 and original index 1150751, selection on the full partial prefix of depth 12 and code 337275 returns the complete row with depth 12, base-four code 337275, original node 1150751, kind 2, reserved field 0, 1445 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84299-1149665", "unmarked_context_11_84299_1149665", "Unmarked parent at depth 11, code 84299",
                "The frontier Boolean is false at remaining fuel 10, original node 1149665, the whole prefixCache at depth 11 and code 84299, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21078-1150558", "unmarked_context_10_21078_1150558", "Unmarked parent at depth 10, code 21078",
                "The frontier Boolean is false at remaining fuel 11, original node 1150558, the whole prefixCache at depth 10 and code 21078, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84299-1149665", "node_context_11_84299_1149665", "Original split at fuel 10 and node 1149665",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1149592, 1149623, 1149664. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21078-1150558", "node_context_10_21078_1150558", "Original split at fuel 11 and node 1150558",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1150371, 1150425, 1150484, 1150557. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-337197-1149592", "context_12_337197_1149592", "Context at depth 12, code 337197, node 1149592",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337197 and original node 1149592, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-337275-1150751", "context_12_337275_1150751", "Context at depth 12, code 337275, node 1150751",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337275 and original node 1150751, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
