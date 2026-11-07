using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0630Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0630.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0630",
        H("Original frontier context coverage 0630"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30245", "selected_cut_30245", "Selected cut at depth 12, code 94139, node 763295",
                "At remaining fuel 9 and original index 763295, selection on the full partial prefix of depth 12 and code 94139 returns the complete row with depth 12, base-four code 94139, original node 763295, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30290", "selected_cut_30290", "Selected cut at depth 13, code 417875, node 764733",
                "At remaining fuel 8 and original index 764733, selection on the full partial prefix of depth 13 and code 417875 returns the complete row with depth 13, base-four code 417875, original node 764733, kind 2, reserved field 0, 849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23534-763296", "unmarked_context_11_23534_763296", "Unmarked parent at depth 11, code 23534",
                "The frontier Boolean is false at remaining fuel 10, original node 763296, the whole prefixCache at depth 11 and code 23534, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26116-764652", "unmarked_context_11_26116_764652", "Unmarked parent at depth 11, code 26116",
                "The frontier Boolean is false at remaining fuel 10, original node 764652, the whole prefixCache at depth 11 and code 26116, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23534-763296", "node_context_11_23534_763296", "Original split at fuel 10 and node 763296",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 763263, 763273, 763285, 763295. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26116-764652", "node_context_11_26116_764652", "Original split at fuel 10 and node 764652",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 307381, 764461, 764551, 764651. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-94139-763295", "context_12_94139_763295", "Context at depth 12, code 94139, node 763295",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 94139 and original node 763295, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-417875-764733", "context_13_417875_764733", "Context at depth 13, code 417875, node 764733",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 417875 and original node 764733, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
