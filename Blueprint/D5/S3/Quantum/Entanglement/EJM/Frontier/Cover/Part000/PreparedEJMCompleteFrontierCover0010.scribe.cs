using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0010Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0010.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0010",
        H("Original frontier context coverage 0010"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00482", "selected_cut_00482", "Selected cut at depth 11, code 359, node 22732",
                "At remaining fuel 10 and original index 22732, selection on the full partial prefix of depth 11 and code 359 returns the complete row with depth 11, base-four code 359, original node 22732, kind 2, reserved field 0, 2897 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00529", "selected_cut_00529", "Selected cut at depth 13, code 6166, node 24507",
                "At remaining fuel 8 and original index 24507, selection on the full partial prefix of depth 13 and code 6166 returns the complete row with depth 13, base-four code 6166, original node 24507, kind 2, reserved field 0, 2325 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-89-22733", "unmarked_context_10_89_22733", "Unmarked parent at depth 10, code 89",
                "The frontier Boolean is false at remaining fuel 11, original node 22733, the whole prefixCache at depth 10 and code 89, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-6164-24415", "unmarked_context_13_6164_24415", "Unmarked parent at depth 13, code 6164",
                "The frontier Boolean is false at remaining fuel 8, original node 24415, the whole prefixCache at depth 13 and code 6164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-89-22733", "node_context_10_89_22733", "Original split at fuel 11 and node 22733",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 22078, 22469, 22610, 22732. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-6164-24415", "node_context_13_6164_24415", "Original split at fuel 8 and node 24415",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 24343, 24371, 24393, 24414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-359-22732", "context_11_359_22732", "Context at depth 11, code 359, node 22732",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 359 and original node 22732, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-6166-24507", "context_13_6166_24507", "Context at depth 13, code 6166, node 24507",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 6166 and original node 24507, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
