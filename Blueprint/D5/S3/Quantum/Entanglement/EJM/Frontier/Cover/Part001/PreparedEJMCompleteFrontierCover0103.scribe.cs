using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0103Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0103.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0103",
        H("Original frontier context coverage 0103"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04947", "selected_cut_04947", "Selected cut at depth 13, code 75144, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 75144 returns the complete row with depth 13, base-four code 75144, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04994", "selected_cut_04994", "Selected cut at depth 13, code 75215, node 156205",
                "At remaining fuel 8 and original index 156205, selection on the full partial prefix of depth 13 and code 75215 returns the complete row with depth 13, base-four code 75215, original node 156205, kind 2, reserved field 0, 973 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18785-155259", "unmarked_context_12_18785_155259", "Unmarked parent at depth 12, code 18785",
                "The frontier Boolean is false at remaining fuel 9, original node 155259, the whole prefixCache at depth 12 and code 18785, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18803-156206", "unmarked_context_12_18803_156206", "Unmarked parent at depth 12, code 18803",
                "The frontier Boolean is false at remaining fuel 9, original node 156206, the whole prefixCache at depth 12 and code 18803, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18785-155259", "node_context_12_18785_155259", "Original split at fuel 9 and node 155259",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 155226, 155248, 155258. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18803-156206", "node_context_12_18803_156206", "Original split at fuel 9 and node 156206",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 156166, 156197, 156205. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18785-155259", "context_12_18785_155259", "Context at depth 12, code 18785, node 155259",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18785 and original node 155259, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_75140_3444, context_13_75141_155226, context_13_75142_155248, context_13_75143_155258.", DescribeRole.Theorem),
            Node("context-12-18803-156206", "context_12_18803_156206", "Context at depth 12, code 18803, node 156206",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18803 and original node 156206, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_75212_3444, context_13_75213_156166, context_13_75214_156197, context_13_75215_156205.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
