using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0507Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0507.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0507",
        H("Original frontier context coverage 0507"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24340", "selected_cut_24340", "Selected cut at depth 13, code 308407, node 615506",
                "At remaining fuel 8 and original index 615506, selection on the full partial prefix of depth 13 and code 308407 returns the complete row with depth 13, base-four code 308407, original node 615506, kind 2, reserved field 0, 885 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24387", "selected_cut_24387", "Selected cut at depth 13, code 308463, node 616489",
                "At remaining fuel 8 and original index 616489, selection on the full partial prefix of depth 13 and code 308463 returns the complete row with depth 13, base-four code 308463, original node 616489, kind 2, reserved field 0, 941 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77101-615507", "unmarked_context_12_77101_615507", "Unmarked parent at depth 12, code 77101",
                "The frontier Boolean is false at remaining fuel 9, original node 615507, the whole prefixCache at depth 12 and code 77101, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77115-616490", "unmarked_context_12_77115_616490", "Unmarked parent at depth 12, code 77115",
                "The frontier Boolean is false at remaining fuel 9, original node 616490, the whole prefixCache at depth 12 and code 77115, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77101-615507", "node_context_12_77101_615507", "Original split at fuel 9 and node 615507",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 615448, 615472, 615494, 615506. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77115-616490", "node_context_12_77115_616490", "Original split at fuel 9 and node 616490",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 616401, 616440, 616468, 616489. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-308407-615506", "context_13_308407_615506", "Context at depth 13, code 308407, node 615506",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 308407 and original node 615506, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77115-616490", "context_12_77115_616490", "Context at depth 12, code 77115, node 616490",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77115 and original node 616490, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_308460_616401, context_13_308461_616440, context_13_308462_616468, context_13_308463_616489.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
