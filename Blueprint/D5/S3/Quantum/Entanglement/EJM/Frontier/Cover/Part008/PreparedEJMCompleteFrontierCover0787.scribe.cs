using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0787Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0787.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0787",
        H("Original frontier context coverage 0787"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37779", "selected_cut_37779", "Selected cut at depth 12, code 300342, node 1012921",
                "At remaining fuel 9 and original index 1012921, selection on the full partial prefix of depth 12 and code 300342 returns the complete row with depth 12, base-four code 300342, original node 1012921, kind 2, reserved field 0, 2441 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37826", "selected_cut_37826", "Selected cut at depth 12, code 300404, node 1014369",
                "At remaining fuel 9 and original index 1014369, selection on the full partial prefix of depth 12 and code 300404 returns the complete row with depth 12, base-four code 300404, original node 1014369, kind 2, reserved field 0, 1777 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75085-1012966", "unmarked_context_11_75085_1012966", "Unmarked parent at depth 11, code 75085",
                "The frontier Boolean is false at remaining fuel 10, original node 1012966, the whole prefixCache at depth 11 and code 75085, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75100-1014335", "unmarked_context_11_75100_1014335", "Unmarked parent at depth 11, code 75100",
                "The frontier Boolean is false at remaining fuel 10, original node 1014335, the whole prefixCache at depth 11 and code 75100, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75085-1012966", "node_context_11_75085_1012966", "Original split at fuel 10 and node 1012966",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1012883, 891951, 1012921, 1012965. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75100-1014335", "node_context_11_75100_1014335", "Original split at fuel 10 and node 1014335",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1014270, 1014291, 1014315, 1014334. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300342-1012921", "context_12_300342_1012921", "Context at depth 12, code 300342, node 1012921",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300342 and original node 1012921, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-300404-1014369", "context_12_300404_1014369", "Context at depth 12, code 300404, node 1014369",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300404 and original node 1014369, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
