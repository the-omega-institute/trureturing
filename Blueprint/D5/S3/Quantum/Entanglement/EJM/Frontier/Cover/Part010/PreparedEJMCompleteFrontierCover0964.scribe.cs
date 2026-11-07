using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0964Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0964.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0964",
        H("Original frontier context coverage 0964"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46275", "selected_cut_46275", "Selected cut at depth 12, code 370245, node 1257136",
                "At remaining fuel 9 and original index 1257136, selection on the full partial prefix of depth 12 and code 370245 returns the complete row with depth 12, base-four code 370245, original node 1257136, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46323", "selected_cut_46323", "Selected cut at depth 12, code 370446, node 1291335",
                "At remaining fuel 9 and original index 1291335, selection on the full partial prefix of depth 12 and code 370446 returns the complete row with depth 12, base-four code 370446, original node 1291335, kind 2, reserved field 0, 3081 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92561-1289676", "unmarked_context_11_92561_1289676", "Unmarked parent at depth 11, code 92561",
                "The frontier Boolean is false at remaining fuel 10, original node 1289676, the whole prefixCache at depth 11 and code 92561, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92610-1291222", "unmarked_context_11_92610_1291222", "Unmarked parent at depth 11, code 92610",
                "The frontier Boolean is false at remaining fuel 10, original node 1291222, the whole prefixCache at depth 11 and code 92610, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92561-1289676", "node_context_11_92561_1289676", "Original split at fuel 10 and node 1289676",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1289585, 1257136, 1289624, 1289675. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92610-1291222", "node_context_11_92610_1291222", "Original split at fuel 10 and node 1291222",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1291072, 1291145, 1291221. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-370245-1257136", "context_12_370245_1257136", "Context at depth 12, code 370245, node 1257136",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370245 and original node 1257136, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-370446-1291335", "context_12_370446_1291335", "Context at depth 12, code 370446, node 1291335",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370446 and original node 1291335, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
