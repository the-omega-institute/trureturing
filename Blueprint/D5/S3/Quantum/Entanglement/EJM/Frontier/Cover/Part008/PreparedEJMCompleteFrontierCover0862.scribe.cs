using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0862Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0862.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0862",
        H("Original frontier context coverage 0862"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41379", "selected_cut_41379", "Selected cut at depth 11, code 83685, node 1131658",
                "At remaining fuel 10 and original index 1131658, selection on the full partial prefix of depth 11 and code 83685 returns the complete row with depth 11, base-four code 83685, original node 1131658, kind 2, reserved field 0, 2161 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41425", "selected_cut_41425", "Selected cut at depth 12, code 335905, node 1132997",
                "At remaining fuel 9 and original index 1132997, selection on the full partial prefix of depth 12 and code 335905 returns the complete row with depth 12, base-four code 335905, original node 1132997, kind 2, reserved field 0, 2041 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-20921-1131756", "unmarked_context_10_20921_1131756", "Unmarked parent at depth 10, code 20921",
                "The frontier Boolean is false at remaining fuel 11, original node 1131756, the whole prefixCache at depth 10 and code 20921, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-20993-1132972", "unmarked_context_10_20993_1132972", "Unmarked parent at depth 10, code 20993",
                "The frontier Boolean is false at remaining fuel 11, original node 1132972, the whole prefixCache at depth 10 and code 20993, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-20921-1131756", "node_context_10_20921_1131756", "Original split at fuel 11 and node 1131756",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1131594, 1131658, 1131705, 1131755. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-20993-1132972", "node_context_10_20993_1132972", "Original split at fuel 11 and node 1132972",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1132727, 1132812, 1132891, 1132971. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-83685-1131658", "context_11_83685_1131658", "Context at depth 11, code 83685, node 1131658",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83685 and original node 1131658, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-335905-1132997", "context_12_335905_1132997", "Context at depth 12, code 335905, node 1132997",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 335905 and original node 1132997, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
