using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0050Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0050.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0050",
        H("Original frontier context coverage 0050"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02403", "selected_cut_02403", "Selected cut at depth 13, code 22728, node 78169",
                "At remaining fuel 8 and original index 78169, selection on the full partial prefix of depth 13 and code 22728 returns the complete row with depth 13, base-four code 22728, original node 78169, kind 2, reserved field 0, 893 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02450", "selected_cut_02450", "Selected cut at depth 13, code 22769, node 79259",
                "At remaining fuel 8 and original index 79259, selection on the full partial prefix of depth 13 and code 22769 returns the complete row with depth 13, base-four code 22769, original node 79259, kind 2, reserved field 0, 3973 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5681-78157", "unmarked_context_12_5681_78157", "Unmarked parent at depth 12, code 5681",
                "The frontier Boolean is false at remaining fuel 9, original node 78157, the whole prefixCache at depth 12 and code 5681, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1422-79207", "unmarked_context_11_1422_79207", "Unmarked parent at depth 11, code 1422",
                "The frontier Boolean is false at remaining fuel 10, original node 79207, the whole prefixCache at depth 11 and code 1422, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5681-78157", "node_context_12_5681_78157", "Original split at fuel 9 and node 78157",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 78070, 78120, 78145, 78156. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1422-79207", "node_context_11_1422_79207", "Original split at fuel 10 and node 79207",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 78880, 78966, 79125, 79206. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5681-78157", "context_12_5681_78157", "Context at depth 12, code 5681, node 78157",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5681 and original node 78157, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_22724_78070, context_13_22725_78120, context_13_22726_78145, context_13_22727_78156.", DescribeRole.Theorem),
            Node("context-13-22769-79259", "context_13_22769_79259", "Context at depth 13, code 22769, node 79259",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22769 and original node 79259, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
