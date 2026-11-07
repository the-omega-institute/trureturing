using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0672Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0672.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0672",
        H("Original frontier context coverage 0672"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32260", "selected_cut_32260", "Selected cut at depth 12, code 107932, node 829040",
                "At remaining fuel 9 and original index 829040, selection on the full partial prefix of depth 12 and code 107932 returns the complete row with depth 12, base-four code 107932, original node 829040, kind 2, reserved field 0, 1813 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32306", "selected_cut_32306", "Selected cut at depth 13, code 433199, node 830448",
                "At remaining fuel 8 and original index 830448, selection on the full partial prefix of depth 13 and code 433199 returns the complete row with depth 13, base-four code 433199, original node 830448, kind 2, reserved field 0, 873 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26982-829017", "unmarked_context_11_26982_829017", "Unmarked parent at depth 11, code 26982",
                "The frontier Boolean is false at remaining fuel 10, original node 829017, the whole prefixCache at depth 11 and code 26982, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27074-830450", "unmarked_context_11_27074_830450", "Unmarked parent at depth 11, code 27074",
                "The frontier Boolean is false at remaining fuel 10, original node 830450, the whole prefixCache at depth 11 and code 27074, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26982-829017", "node_context_11_26982_829017", "Original split at fuel 10 and node 829017",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 828976, 828995, 813979, 829016. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27074-830450", "node_context_11_27074_830450", "Original split at fuel 10 and node 830450",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 4595, 830068, 4595, 830449. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-26982-829017", "context_11_26982_829017", "Context at depth 11, code 26982, node 829017",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 26982 and original node 829017, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_107928_828976, context_12_107929_828995, context_12_107930_813979, context_12_107931_829016.", DescribeRole.Theorem),
            Node("context-11-27074-830450", "context_11_27074_830450", "Context at depth 11, code 27074, node 830450",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27074 and original node 830450, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_108296_4595, context_12_108297_830068, context_12_108298_4595, context_12_108299_830449.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
