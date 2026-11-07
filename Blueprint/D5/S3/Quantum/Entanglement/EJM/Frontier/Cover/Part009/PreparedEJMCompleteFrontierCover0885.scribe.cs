using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0885Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0885.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0885",
        H("Original frontier context coverage 0885"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42483", "selected_cut_42483", "Selected cut at depth 11, code 84516, node 1160881",
                "At remaining fuel 10 and original index 1160881, selection on the full partial prefix of depth 11 and code 84516 returns the complete row with depth 11, base-four code 84516, original node 1160881, kind 2, reserved field 0, 3537 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42530", "selected_cut_42530", "Selected cut at depth 12, code 338210, node 1162257",
                "At remaining fuel 9 and original index 1162257, selection on the full partial prefix of depth 12 and code 338210 returns the complete row with depth 12, base-four code 338210, original node 1162257, kind 2, reserved field 0, 2117 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21128-1160830", "unmarked_context_10_21128_1160830", "Unmarked parent at depth 10, code 21128",
                "The frontier Boolean is false at remaining fuel 11, original node 1160830, the whole prefixCache at depth 10 and code 21128, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21137-1162183", "unmarked_context_10_21137_1162183", "Unmarked parent at depth 10, code 21137",
                "The frontier Boolean is false at remaining fuel 11, original node 1162183, the whole prefixCache at depth 10 and code 21137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21128-1160830", "node_context_10_21128_1160830", "Original split at fuel 11 and node 1160830",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1160647, 1160721, 1160768, 1160829. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21137-1162183", "node_context_10_21137_1162183", "Original split at fuel 11 and node 1162183",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1161914, 1161962, 1162092, 1162182. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-21128-1160830", "context_10_21128_1160830", "Context at depth 10, code 21128, node 1160830",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21128 and original node 1160830, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_84512_1160647, context_11_84513_1160721, context_11_84514_1160768, context_11_84515_1160829.", DescribeRole.Theorem),
            Node("context-12-338210-1162257", "context_12_338210_1162257", "Context at depth 12, code 338210, node 1162257",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338210 and original node 1162257, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
