using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1013Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1013.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1013",
        H("Original frontier context coverage 1013"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48626", "selected_cut_48626", "Selected cut at depth 12, code 401696, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 401696 returns the complete row with depth 12, base-four code 401696, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48674", "selected_cut_48674", "Selected cut at depth 12, code 402227, node 1367068",
                "At remaining fuel 9 and original index 1367068, selection on the full partial prefix of depth 12 and code 402227 returns the complete row with depth 12, base-four code 402227, original node 1367068, kind 2, reserved field 0, 1245 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-100424-1365157", "unmarked_context_11_100424_1365157", "Unmarked parent at depth 11, code 100424",
                "The frontier Boolean is false at remaining fuel 10, original node 1365157, the whole prefixCache at depth 11 and code 100424, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-100556-1367069", "unmarked_context_11_100556_1367069", "Unmarked parent at depth 11, code 100556",
                "The frontier Boolean is false at remaining fuel 10, original node 1367069, the whole prefixCache at depth 11 and code 100556, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-100424-1365157", "node_context_11_100424_1365157", "Original split at fuel 10 and node 1365157",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1365066, 1365118, 1365156. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-100556-1367069", "node_context_11_100556_1367069", "Original split at fuel 10 and node 1367069",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1367004, 1367038, 1367068. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-401696-1108174", "context_12_401696_1108174", "Context at depth 12, code 401696, node 1108174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 401696 and original node 1108174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-100556-1367069", "context_11_100556_1367069", "Context at depth 11, code 100556, node 1367069",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 100556 and original node 1367069, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_402224_1108174, context_12_402225_1367004, context_12_402226_1367038, context_12_402227_1367068.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
