using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0826Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0826.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0826",
        H("Original frontier context coverage 0826"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39651", "selected_cut_39651", "Selected cut at depth 11, code 76914, node 1076019",
                "At remaining fuel 10 and original index 1076019, selection on the full partial prefix of depth 11 and code 76914 returns the complete row with depth 11, base-four code 76914, original node 1076019, kind 2, reserved field 0, 1849 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39698", "selected_cut_39698", "Selected cut at depth 13, code 1230929, node 1077135",
                "At remaining fuel 8 and original index 1077135, selection on the full partial prefix of depth 13 and code 1230929 returns the complete row with depth 13, base-four code 1230929, original node 1077135, kind 2, reserved field 0, 1393 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-19228-1076048", "unmarked_context_10_19228_1076048", "Unmarked parent at depth 10, code 19228",
                "The frontier Boolean is false at remaining fuel 11, original node 1076048, the whole prefixCache at depth 10 and code 19228, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-76932-1077074", "unmarked_context_11_76932_1077074", "Unmarked parent at depth 11, code 76932",
                "The frontier Boolean is false at remaining fuel 10, original node 1077074, the whole prefixCache at depth 11 and code 76932, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-19228-1076048", "node_context_10_19228_1076048", "Original split at fuel 11 and node 1076048",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1076002, 1076019, 1076047. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-76932-1077074", "node_context_11_76932_1077074", "Original split at fuel 10 and node 1077074",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1076974, 1077023, 1077073. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-76914-1076019", "context_11_76914_1076019", "Context at depth 11, code 76914, node 1076019",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 76914 and original node 1076019, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1230929-1077135", "context_13_1230929_1077135", "Context at depth 13, code 1230929, node 1077135",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1230929 and original node 1077135, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
