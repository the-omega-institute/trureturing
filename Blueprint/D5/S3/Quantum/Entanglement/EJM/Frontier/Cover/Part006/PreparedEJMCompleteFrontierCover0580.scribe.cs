using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0580Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0580.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0580",
        H("Original frontier context coverage 0580"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27843", "selected_cut_27843", "Selected cut at depth 13, code 367716, node 703898",
                "At remaining fuel 8 and original index 703898, selection on the full partial prefix of depth 13 and code 367716 returns the complete row with depth 13, base-four code 367716, original node 703898, kind 2, reserved field 0, 1777 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27891", "selected_cut_27891", "Selected cut at depth 13, code 367767, node 704747",
                "At remaining fuel 8 and original index 704747, selection on the full partial prefix of depth 13 and code 367767 returns the complete row with depth 13, base-four code 367767, original node 704747, kind 2, reserved field 0, 585 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91929-703966", "unmarked_context_12_91929_703966", "Unmarked parent at depth 12, code 91929",
                "The frontier Boolean is false at remaining fuel 9, original node 703966, the whole prefixCache at depth 12 and code 91929, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91940-704688", "unmarked_context_12_91940_704688", "Unmarked parent at depth 12, code 91940",
                "The frontier Boolean is false at remaining fuel 9, original node 704688, the whole prefixCache at depth 12 and code 91940, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91929-703966", "node_context_12_91929_703966", "Original split at fuel 9 and node 703966",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 703898, 703932, 703958, 703965. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91940-704688", "node_context_12_91940_704688", "Original split at fuel 9 and node 704688",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 704635, 704668, 704683, 704687. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-367716-703898", "context_13_367716_703898", "Context at depth 13, code 367716, node 703898",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367716 and original node 703898, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-367767-704747", "context_13_367767_704747", "Context at depth 13, code 367767, node 704747",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367767 and original node 704747, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
