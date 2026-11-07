using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0402Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0402.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0402",
        H("Original frontier context coverage 0402"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19298", "selected_cut_19298", "Selected cut at depth 12, code 72080, node 492941",
                "At remaining fuel 9 and original index 492941, selection on the full partial prefix of depth 12 and code 72080 returns the complete row with depth 12, base-four code 72080, original node 492941, kind 2, reserved field 0, 2441 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19346", "selected_cut_19346", "Selected cut at depth 12, code 72131, node 494053",
                "At remaining fuel 9 and original index 494053, selection on the full partial prefix of depth 12 and code 72131 returns the complete row with depth 12, base-four code 72131, original node 494053, kind 2, reserved field 0, 1109 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18020-493059", "unmarked_context_11_18020_493059", "Unmarked parent at depth 11, code 18020",
                "The frontier Boolean is false at remaining fuel 10, original node 493059, the whole prefixCache at depth 11 and code 18020, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1126-494004", "unmarked_context_9_1126_494004", "Unmarked parent at depth 9, code 1126",
                "The frontier Boolean is false at remaining fuel 12, original node 494004, the whole prefixCache at depth 9 and code 1126, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18020-493059", "node_context_11_18020_493059", "Original split at fuel 10 and node 493059",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 492941, 492963, 493023, 493058. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1126-494004", "node_context_9_1126_494004", "Original split at fuel 12 and node 494004",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 492921, 493445, 493701, 494003. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-72080-492941", "context_12_72080_492941", "Context at depth 12, code 72080, node 492941",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72080 and original node 492941, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-72131-494053", "context_12_72131_494053", "Context at depth 12, code 72131, node 494053",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72131 and original node 494053, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
