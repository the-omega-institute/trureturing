using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0118Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0118.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0118",
        H("Original frontier context coverage 0118"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05667", "selected_cut_05667", "Selected cut at depth 12, code 20772, node 174738",
                "At remaining fuel 9 and original index 174738, selection on the full partial prefix of depth 12 and code 20772 returns the complete row with depth 12, base-four code 20772, original node 174738, kind 2, reserved field 0, 3917 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05712", "selected_cut_05712", "Selected cut at depth 10, code 1299, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 1299 returns the complete row with depth 10, base-four code 1299, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-20771-174678", "unmarked_context_12_20771_174678", "Unmarked parent at depth 12, code 20771",
                "The frontier Boolean is false at remaining fuel 9, original node 174678, the whole prefixCache at depth 12 and code 20771, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-324-175519", "unmarked_context_9_324_175519", "Unmarked parent at depth 9, code 324",
                "The frontier Boolean is false at remaining fuel 12, original node 175519, the whole prefixCache at depth 9 and code 324, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-20771-174678", "node_context_12_20771_174678", "Original split at fuel 9 and node 174678",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 174621, 174648, 174666, 174677. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-324-175519", "node_context_9_324_175519", "Original split at fuel 12 and node 175519",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 173618, 174383, 175518, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-20771-174678", "context_12_20771_174678", "Context at depth 12, code 20771, node 174678",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20771 and original node 174678, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_83084_174621, context_13_83085_174648, context_13_83086_174666, context_13_83087_174677.", DescribeRole.Theorem),
            Node("context-9-324-175519", "context_9_324_175519", "Context at depth 9, code 324, node 175519",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 324 and original node 175519, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1296_173618, context_10_1297_174383, context_10_1298_175518, context_10_1299_3440.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
