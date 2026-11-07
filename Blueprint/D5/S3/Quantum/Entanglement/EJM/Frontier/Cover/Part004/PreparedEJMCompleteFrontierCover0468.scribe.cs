using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0468Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0468.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0468",
        H("Original frontier context coverage 0468"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22467", "selected_cut_22467", "Selected cut at depth 12, code 75657, node 571899",
                "At remaining fuel 9 and original index 571899, selection on the full partial prefix of depth 12 and code 75657 returns the complete row with depth 12, base-four code 75657, original node 571899, kind 2, reserved field 0, 2305 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22515", "selected_cut_22515", "Selected cut at depth 12, code 75705, node 572967",
                "At remaining fuel 9 and original index 572967, selection on the full partial prefix of depth 12 and code 75705 returns the complete row with depth 12, base-four code 75705, original node 572967, kind 2, reserved field 0, 1253 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18914-571972", "unmarked_context_11_18914_571972", "Unmarked parent at depth 11, code 18914",
                "The frontier Boolean is false at remaining fuel 10, original node 571972, the whole prefixCache at depth 11 and code 18914, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18925-572929", "unmarked_context_11_18925_572929", "Unmarked parent at depth 11, code 18925",
                "The frontier Boolean is false at remaining fuel 10, original node 572929, the whole prefixCache at depth 11 and code 18925, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18914-571972", "node_context_11_18914_571972", "Original split at fuel 10 and node 571972",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 571868, 571899, 571934, 571971. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18925-572929", "node_context_11_18925_572929", "Original split at fuel 10 and node 572929",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 572881, 572893, 572914, 572928. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75657-571899", "context_12_75657_571899", "Context at depth 12, code 75657, node 571899",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75657 and original node 571899, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75705-572967", "context_12_75705_572967", "Context at depth 12, code 75705, node 572967",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75705 and original node 572967, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
