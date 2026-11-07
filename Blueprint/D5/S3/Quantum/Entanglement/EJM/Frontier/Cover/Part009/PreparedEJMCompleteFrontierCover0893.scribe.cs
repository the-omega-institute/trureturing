using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0893Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0893.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0893",
        H("Original frontier context coverage 0893"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42867", "selected_cut_42867", "Selected cut at depth 11, code 84720, node 1171217",
                "At remaining fuel 10 and original index 1171217, selection on the full partial prefix of depth 11 and code 84720 returns the complete row with depth 11, base-four code 84720, original node 1171217, kind 2, reserved field 0, 1133 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42915", "selected_cut_42915", "Selected cut at depth 12, code 338991, node 1173117",
                "At remaining fuel 9 and original index 1173117, selection on the full partial prefix of depth 12 and code 338991 returns the complete row with depth 12, base-four code 338991, original node 1173117, kind 2, reserved field 0, 2841 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21180-1171282", "unmarked_context_10_21180_1171282", "Unmarked parent at depth 10, code 21180",
                "The frontier Boolean is false at remaining fuel 11, original node 1171282, the whole prefixCache at depth 10 and code 21180, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84746-1172974", "unmarked_context_11_84746_1172974", "Unmarked parent at depth 11, code 84746",
                "The frontier Boolean is false at remaining fuel 10, original node 1172974, the whole prefixCache at depth 11 and code 84746, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21180-1171282", "node_context_10_21180_1171282", "Original split at fuel 11 and node 1171282",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1171217, 1171244, 1171266, 1171281. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84746-1172974", "node_context_11_84746_1172974", "Original split at fuel 10 and node 1172974",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1172909, 1172910, 1172973. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84720-1171217", "context_11_84720_1171217", "Context at depth 11, code 84720, node 1171217",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84720 and original node 1171217, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-338991-1173117", "context_12_338991_1173117", "Context at depth 12, code 338991, node 1173117",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338991 and original node 1173117, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
