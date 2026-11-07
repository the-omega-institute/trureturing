using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0658Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0658.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0658",
        H("Original frontier context coverage 0658"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31588", "selected_cut_31588", "Selected cut at depth 13, code 424219, node 810431",
                "At remaining fuel 8 and original index 810431, selection on the full partial prefix of depth 13 and code 424219 returns the complete row with depth 13, base-four code 424219, original node 810431, kind 2, reserved field 0, 813 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31635", "selected_cut_31635", "Selected cut at depth 13, code 424269, node 811231",
                "At remaining fuel 8 and original index 811231, selection on the full partial prefix of depth 13 and code 424269 returns the complete row with depth 13, base-four code 424269, original node 811231, kind 2, reserved field 0, 2373 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-106054-810432", "unmarked_context_12_106054_810432", "Unmarked parent at depth 12, code 106054",
                "The frontier Boolean is false at remaining fuel 9, original node 810432, the whole prefixCache at depth 12 and code 106054, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-106066-811189", "unmarked_context_12_106066_811189", "Unmarked parent at depth 12, code 106066",
                "The frontier Boolean is false at remaining fuel 9, original node 811189, the whole prefixCache at depth 12 and code 106066, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-106054-810432", "node_context_12_106054_810432", "Original split at fuel 9 and node 810432",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 810400, 810423, 810431. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-106066-811189", "node_context_12_106066_811189", "Original split at fuel 9 and node 811189",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 811158, 811178, 811188. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-424219-810431", "context_13_424219_810431", "Context at depth 13, code 424219, node 810431",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424219 and original node 810431, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-424269-811231", "context_13_424269_811231", "Context at depth 13, code 424269, node 811231",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424269 and original node 811231, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
