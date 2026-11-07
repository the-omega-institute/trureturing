using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0792Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0792.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0792",
        H("Original frontier context coverage 0792"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38020", "selected_cut_38020", "Selected cut at depth 11, code 75184, node 1021573",
                "At remaining fuel 10 and original index 1021573, selection on the full partial prefix of depth 11 and code 75184 returns the complete row with depth 11, base-four code 75184, original node 1021573, kind 2, reserved field 0, 2845 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38066", "selected_cut_38066", "Selected cut at depth 12, code 300818, node 1022813",
                "At remaining fuel 9 and original index 1022813, selection on the full partial prefix of depth 12 and code 300818 returns the complete row with depth 12, base-four code 300818, original node 1022813, kind 2, reserved field 0, 3077 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18795-1021530", "unmarked_context_10_18795_1021530", "Unmarked parent at depth 10, code 18795",
                "The frontier Boolean is false at remaining fuel 11, original node 1021530, the whole prefixCache at depth 10 and code 18795, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18800-1022669", "unmarked_context_10_18800_1022669", "Unmarked parent at depth 10, code 18800",
                "The frontier Boolean is false at remaining fuel 11, original node 1022669, the whole prefixCache at depth 10 and code 18800, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18795-1021530", "node_context_10_18795_1021530", "Original split at fuel 11 and node 1021530",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1021422, 1021456, 1021490, 1021529. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18800-1022669", "node_context_10_18800_1022669", "Original split at fuel 11 and node 1022669",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 167448, 1022136, 1022460, 1022668. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-18795-1021530", "context_10_18795_1021530", "Context at depth 10, code 18795, node 1021530",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18795 and original node 1021530, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_75180_1021422, context_11_75181_1021456, context_11_75182_1021490, context_11_75183_1021529.", DescribeRole.Theorem),
            Node("context-12-300818-1022813", "context_12_300818_1022813", "Context at depth 12, code 300818, node 1022813",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300818 and original node 1022813, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
