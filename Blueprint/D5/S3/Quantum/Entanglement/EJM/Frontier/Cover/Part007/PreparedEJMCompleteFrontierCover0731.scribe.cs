using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0731Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0731.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0731",
        H("Original frontier context coverage 0731"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35090", "selected_cut_35090", "Selected cut at depth 12, code 284033, node 918573",
                "At remaining fuel 9 and original index 918573, selection on the full partial prefix of depth 12 and code 284033 returns the complete row with depth 12, base-four code 284033, original node 918573, kind 2, reserved field 0, 1329 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35138", "selected_cut_35138", "Selected cut at depth 12, code 284198, node 920874",
                "At remaining fuel 9 and original index 920874, selection on the full partial prefix of depth 12 and code 284198 returns the complete row with depth 12, base-four code 284198, original node 920874, kind 2, reserved field 0, 2657 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71008-918625", "unmarked_context_11_71008_918625", "Unmarked parent at depth 11, code 71008",
                "The frontier Boolean is false at remaining fuel 10, original node 918625, the whole prefixCache at depth 11 and code 71008, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71048-920756", "unmarked_context_11_71048_920756", "Unmarked parent at depth 11, code 71048",
                "The frontier Boolean is false at remaining fuel 10, original node 920756, the whole prefixCache at depth 11 and code 71048, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71008-918625", "node_context_11_71008_918625", "Original split at fuel 10 and node 918625",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 918545, 918573, 918596, 918624. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71048-920756", "node_context_11_71048_920756", "Original split at fuel 10 and node 920756",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 920602, 920636, 920698, 920755. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-284033-918573", "context_12_284033_918573", "Context at depth 12, code 284033, node 918573",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 284033 and original node 918573, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-284198-920874", "context_12_284198_920874", "Context at depth 12, code 284198, node 920874",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 284198 and original node 920874, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
