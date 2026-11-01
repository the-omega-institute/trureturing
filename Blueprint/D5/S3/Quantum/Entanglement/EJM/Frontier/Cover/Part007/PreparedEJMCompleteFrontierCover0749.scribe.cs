using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0749Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0749.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0749",
        H("Original frontier context coverage 0749"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35955", "selected_cut_35955", "Selected cut at depth 10, code 17973, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 17973 returns the complete row with depth 10, base-four code 17973, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36002", "selected_cut_36002", "Selected cut at depth 12, code 287639, node 949001",
                "At remaining fuel 9 and original index 949001, selection on the full partial prefix of depth 12 and code 287639 returns the complete row with depth 12, base-four code 287639, original node 949001, kind 2, reserved field 0, 1237 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17972-948022", "unmarked_context_10_17972_948022", "Unmarked parent at depth 10, code 17972",
                "The frontier Boolean is false at remaining fuel 11, original node 948022, the whole prefixCache at depth 10 and code 17972, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71909-949002", "unmarked_context_11_71909_949002", "Unmarked parent at depth 11, code 71909",
                "The frontier Boolean is false at remaining fuel 10, original node 949002, the whole prefixCache at depth 11 and code 71909, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17972-948022", "node_context_10_17972_948022", "Original split at fuel 11 and node 948022",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 947834, 947954, 948021. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71909-949002", "node_context_11_71909_949002", "Original split at fuel 10 and node 949002",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 948953, 948968, 948984, 949001. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-17972-948022", "context_10_17972_948022", "Context at depth 10, code 17972, node 948022",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17972 and original node 948022, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_71888_907917, context_11_71889_947834, context_11_71890_947954, context_11_71891_948021.", DescribeRole.Theorem),
            Node("context-11-71909-949002", "context_11_71909_949002", "Context at depth 11, code 71909, node 949002",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71909 and original node 949002, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_287636_948953, context_12_287637_948968, context_12_287638_948984, context_12_287639_949001.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
