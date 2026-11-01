using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0889Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0889.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0889",
        H("Original frontier context coverage 0889"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42675", "selected_cut_42675", "Selected cut at depth 12, code 338496, node 1120586",
                "At remaining fuel 9 and original index 1120586, selection on the full partial prefix of depth 12 and code 338496 returns the complete row with depth 12, base-four code 338496, original node 1120586, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42723", "selected_cut_42723", "Selected cut at depth 12, code 338574, node 1167200",
                "At remaining fuel 9 and original index 1167200, selection on the full partial prefix of depth 12 and code 338574 returns the complete row with depth 12, base-four code 338574, original node 1167200, kind 2, reserved field 0, 1077 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5288-1166066", "unmarked_context_9_5288_1166066", "Unmarked parent at depth 9, code 5288",
                "The frontier Boolean is false at remaining fuel 12, original node 1166066, the whole prefixCache at depth 9 and code 5288, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84641-1167101", "unmarked_context_11_84641_1167101", "Unmarked parent at depth 11, code 84641",
                "The frontier Boolean is false at remaining fuel 10, original node 1167101, the whole prefixCache at depth 11 and code 84641, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5288-1166066", "node_context_9_5288_1166066", "Original split at fuel 12 and node 1166066",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1164701, 1165258, 1165636, 1166065. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84641-1167101", "node_context_11_84641_1167101", "Original split at fuel 10 and node 1167101",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1167044, 1167060, 1167080, 1167100. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-5288-1166066", "context_9_5288_1166066", "Context at depth 9, code 5288, node 1166066",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5288 and original node 1166066, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_21152_1164701, context_10_21153_1165258, context_10_21154_1165636, context_10_21155_1166065.", DescribeRole.Theorem),
            Node("context-12-338574-1167200", "context_12_338574_1167200", "Context at depth 12, code 338574, node 1167200",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338574 and original node 1167200, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
