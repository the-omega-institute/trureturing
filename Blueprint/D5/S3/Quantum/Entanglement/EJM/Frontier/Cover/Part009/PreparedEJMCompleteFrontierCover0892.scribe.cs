using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0892Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0892.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0892",
        H("Original frontier context coverage 0892"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42819", "selected_cut_42819", "Selected cut at depth 12, code 338784, node 1169866",
                "At remaining fuel 9 and original index 1169866, selection on the full partial prefix of depth 12 and code 338784 returns the complete row with depth 12, base-four code 338784, original node 1169866, kind 2, reserved field 0, 1621 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42866", "selected_cut_42866", "Selected cut at depth 11, code 84719, node 1171200",
                "At remaining fuel 10 and original index 1171200, selection on the full partial prefix of depth 11 and code 84719 returns the complete row with depth 11, base-four code 84719, original node 1171200, kind 2, reserved field 0, 1377 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84696-1169952", "unmarked_context_11_84696_1169952", "Unmarked parent at depth 11, code 84696",
                "The frontier Boolean is false at remaining fuel 10, original node 1169952, the whole prefixCache at depth 11 and code 84696, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5294-1171202", "unmarked_context_9_5294_1171202", "Unmarked parent at depth 9, code 5294",
                "The frontier Boolean is false at remaining fuel 12, original node 1171202, the whole prefixCache at depth 9 and code 5294, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84696-1169952", "node_context_11_84696_1169952", "Original split at fuel 10 and node 1169952",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1169866, 1169893, 1169923, 1169951. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5294-1171202", "node_context_9_5294_1171202", "Original split at fuel 12 and node 1171202",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1170710, 1170943, 1171017, 1171201. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-338784-1169866", "context_12_338784_1169866", "Context at depth 12, code 338784, node 1169866",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338784 and original node 1169866, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-5294-1171202", "context_9_5294_1171202", "Context at depth 9, code 5294, node 1171202",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5294 and original node 1171202, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_21176_1170710, context_10_21177_1170943, context_10_21178_1171017, context_10_21179_1171201.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
