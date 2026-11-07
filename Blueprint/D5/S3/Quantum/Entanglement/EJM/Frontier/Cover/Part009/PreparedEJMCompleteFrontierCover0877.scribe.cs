using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0877Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0877.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0877",
        H("Original frontier context coverage 0877"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42100", "selected_cut_42100", "Selected cut at depth 11, code 84319, node 1150800",
                "At remaining fuel 10 and original index 1150800, selection on the full partial prefix of depth 11 and code 84319 returns the complete row with depth 11, base-four code 84319, original node 1150800, kind 2, reserved field 0, 3649 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42146", "selected_cut_42146", "Selected cut at depth 12, code 337427, node 1152026",
                "At remaining fuel 9 and original index 1152026, selection on the full partial prefix of depth 12 and code 337427 returns the complete row with depth 12, base-four code 337427, original node 1152026, kind 2, reserved field 0, 3125 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84318-1150752", "unmarked_context_11_84318_1150752", "Unmarked parent at depth 11, code 84318",
                "The frontier Boolean is false at remaining fuel 10, original node 1150752, the whole prefixCache at depth 11 and code 84318, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21088-1151899", "unmarked_context_10_21088_1151899", "Unmarked parent at depth 10, code 21088",
                "The frontier Boolean is false at remaining fuel 11, original node 1151899, the whole prefixCache at depth 10 and code 21088, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84318-1150752", "node_context_11_84318_1150752", "Original split at fuel 10 and node 1150752",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1150693, 1150712, 1150733, 1150751. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21088-1151899", "node_context_10_21088_1151899", "Original split at fuel 11 and node 1151899",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1151636, 1151758, 1151898. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84318-1150752", "context_11_84318_1150752", "Context at depth 11, code 84318, node 1150752",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84318 and original node 1150752, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_337272_1150693, context_12_337273_1150712, context_12_337274_1150733, context_12_337275_1150751.", DescribeRole.Theorem),
            Node("context-12-337427-1152026", "context_12_337427_1152026", "Context at depth 12, code 337427, node 1152026",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337427 and original node 1152026, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
