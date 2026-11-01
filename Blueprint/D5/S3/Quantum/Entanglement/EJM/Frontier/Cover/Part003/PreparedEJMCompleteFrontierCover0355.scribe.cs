using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0355Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0355.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0355",
        H("Original frontier context coverage 0355"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17044", "selected_cut_17044", "Selected cut at depth 12, code 28552, node 433326",
                "At remaining fuel 9 and original index 433326, selection on the full partial prefix of depth 12 and code 28552 returns the complete row with depth 12, base-four code 28552, original node 433326, kind 2, reserved field 0, 3265 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17091", "selected_cut_17091", "Selected cut at depth 12, code 28599, node 434354",
                "At remaining fuel 9 and original index 434354, selection on the full partial prefix of depth 12 and code 28599 returns the complete row with depth 12, base-four code 28599, original node 434354, kind 2, reserved field 0, 1241 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7137-433279", "unmarked_context_11_7137_433279", "Unmarked parent at depth 11, code 7137",
                "The frontier Boolean is false at remaining fuel 10, original node 433279, the whole prefixCache at depth 11 and code 7137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7149-434355", "unmarked_context_11_7149_434355", "Unmarked parent at depth 11, code 7149",
                "The frontier Boolean is false at remaining fuel 10, original node 434355, the whole prefixCache at depth 11 and code 7149, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7137-433279", "node_context_11_7137_433279", "Original split at fuel 10 and node 433279",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 433190, 433214, 433238, 433278. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7149-434355", "node_context_11_7149_434355", "Original split at fuel 10 and node 434355",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 434313, 434329, 434343, 434354. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-7137-433279", "context_11_7137_433279", "Context at depth 11, code 7137, node 433279",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 7137 and original node 433279, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_28548_433190, context_12_28549_433214, context_12_28550_433238, context_12_28551_433278.", DescribeRole.Theorem),
            Node("context-11-7149-434355", "context_11_7149_434355", "Context at depth 11, code 7149, node 434355",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 7149 and original node 434355, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_28596_434313, context_12_28597_434329, context_12_28598_434343, context_12_28599_434354.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
