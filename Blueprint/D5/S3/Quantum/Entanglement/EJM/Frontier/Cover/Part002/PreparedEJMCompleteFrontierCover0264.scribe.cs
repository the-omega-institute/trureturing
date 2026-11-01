using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0264Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0264.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0264",
        H("Original frontier context coverage 0264"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12676", "selected_cut_12676", "Selected cut at depth 12, code 26287, node 334137",
                "At remaining fuel 9 and original index 334137, selection on the full partial prefix of depth 12 and code 26287 returns the complete row with depth 12, base-four code 26287, original node 334137, kind 2, reserved field 0, 1605 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12722", "selected_cut_12722", "Selected cut at depth 13, code 105497, node 335227",
                "At remaining fuel 8 and original index 335227, selection on the full partial prefix of depth 13 and code 105497 returns the complete row with depth 13, base-four code 105497, original node 335227, kind 2, reserved field 0, 3917 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6571-334138", "unmarked_context_11_6571_334138", "Unmarked parent at depth 11, code 6571",
                "The frontier Boolean is false at remaining fuel 10, original node 334138, the whole prefixCache at depth 11 and code 6571, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26373-335095", "unmarked_context_12_26373_335095", "Unmarked parent at depth 12, code 26373",
                "The frontier Boolean is false at remaining fuel 9, original node 335095, the whole prefixCache at depth 12 and code 26373, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6571-334138", "node_context_11_6571_334138", "Original split at fuel 10 and node 334138",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 334091, 334109, 334121, 334137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26373-335095", "node_context_12_26373_335095", "Original split at fuel 9 and node 335095",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 334937, 335033, 335082, 335094. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26287-334137", "context_12_26287_334137", "Context at depth 12, code 26287, node 334137",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26287 and original node 334137, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-105497-335227", "context_13_105497_335227", "Context at depth 13, code 105497, node 335227",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105497 and original node 335227, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
