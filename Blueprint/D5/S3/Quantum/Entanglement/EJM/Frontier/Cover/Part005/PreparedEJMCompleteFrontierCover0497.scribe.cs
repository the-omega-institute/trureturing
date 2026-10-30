using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0497Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0497.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0497",
        H("Original frontier context coverage 0497"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23860", "selected_cut_23860", "Selected cut at depth 12, code 76696, node 602727",
                "At remaining fuel 9 and original index 602727, selection on the full partial prefix of depth 12 and code 76696 returns the complete row with depth 12, base-four code 76696, original node 602727, kind 2, reserved field 0, 1965 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23906", "selected_cut_23906", "Selected cut at depth 10, code 4799, node 603598",
                "At remaining fuel 11 and original index 603598, selection on the full partial prefix of depth 10 and code 4799 returns the complete row with depth 10, base-four code 4799, original node 603598, kind 2, reserved field 0, 1529 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19173-602707", "unmarked_context_11_19173_602707", "Unmarked parent at depth 11, code 19173",
                "The frontier Boolean is false at remaining fuel 10, original node 602707, the whole prefixCache at depth 11 and code 19173, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1199-603599", "unmarked_context_9_1199_603599", "Unmarked parent at depth 9, code 1199",
                "The frontier Boolean is false at remaining fuel 12, original node 603599, the whole prefixCache at depth 9 and code 1199, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19173-602707", "node_context_11_19173_602707", "Original split at fuel 10 and node 602707",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 602630, 602653, 602688, 602706. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1199-603599", "node_context_9_1199_603599", "Original split at fuel 12 and node 603599",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 603409, 603507, 603563, 603598. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19173-602707", "context_11_19173_602707", "Context at depth 11, code 19173, node 602707",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19173 and original node 602707, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_76692_602630, context_12_76693_602653, context_12_76694_602688, context_12_76695_602706.", DescribeRole.Theorem),
            Node("context-9-1199-603599", "context_9_1199_603599", "Context at depth 9, code 1199, node 603599",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1199 and original node 603599, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_4796_603409, context_10_4797_603507, context_10_4798_603563, context_10_4799_603598.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
