using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0943Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0943.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0943",
        H("Original frontier context coverage 0943"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45268", "selected_cut_45268", "Selected cut at depth 10, code 22270, node 1252288",
                "At remaining fuel 11 and original index 1252288, selection on the full partial prefix of depth 10 and code 22270 returns the complete row with depth 10, base-four code 22270, original node 1252288, kind 2, reserved field 0, 1185 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45314", "selected_cut_45314", "Selected cut at depth 12, code 367109, node 1254593",
                "At remaining fuel 9 and original index 1254593, selection on the full partial prefix of depth 12 and code 367109 returns the complete row with depth 12, base-four code 367109, original node 1254593, kind 2, reserved field 0, 3121 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5567-1252298", "unmarked_context_9_5567_1252298", "Unmarked parent at depth 9, code 5567",
                "The frontier Boolean is false at remaining fuel 12, original node 1252298, the whole prefixCache at depth 9 and code 5567, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1432-1254454", "unmarked_context_8_1432_1254454", "Unmarked parent at depth 8, code 1432",
                "The frontier Boolean is false at remaining fuel 13, original node 1254454, the whole prefixCache at depth 8 and code 1432, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5567-1252298", "node_context_9_5567_1252298", "Original split at fuel 12 and node 1252298",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1252210, 1252250, 1252288, 1252297. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1432-1254454", "node_context_8_1432_1254454", "Original split at fuel 13 and node 1254454",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1254163, 1254422, 1254451, 1254453. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22270-1252288", "context_10_22270_1252288", "Context at depth 10, code 22270, node 1252288",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22270 and original node 1252288, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-367109-1254593", "context_12_367109_1254593", "Context at depth 12, code 367109, node 1254593",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 367109 and original node 1254593, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
