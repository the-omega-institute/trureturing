using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0927Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0927.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0927",
        H("Original frontier context coverage 0927"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44499", "selected_cut_44499", "Selected cut at depth 12, code 354330, node 1224698",
                "At remaining fuel 9 and original index 1224698, selection on the full partial prefix of depth 12 and code 354330 returns the complete row with depth 12, base-four code 354330, original node 1224698, kind 2, reserved field 0, 2777 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44546", "selected_cut_44546", "Selected cut at depth 11, code 88601, node 1226280",
                "At remaining fuel 10 and original index 1226280, selection on the full partial prefix of depth 11 and code 88601 returns the complete row with depth 11, base-four code 88601, original node 1226280, kind 2, reserved field 0, 4045 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88582-1224773", "unmarked_context_11_88582_1224773", "Unmarked parent at depth 11, code 88582",
                "The frontier Boolean is false at remaining fuel 10, original node 1224773, the whole prefixCache at depth 11 and code 88582, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22148-1226170", "unmarked_context_10_22148_1226170", "Unmarked parent at depth 10, code 22148",
                "The frontier Boolean is false at remaining fuel 11, original node 1226170, the whole prefixCache at depth 10 and code 22148, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88582-1224773", "node_context_11_88582_1224773", "Original split at fuel 10 and node 1224773",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 449505, 1224643, 1224698, 1224772. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22148-1226170", "node_context_10_22148_1226170", "Original split at fuel 11 and node 1226170",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1225942, 1226029, 1226094, 1226169. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-354330-1224698", "context_12_354330_1224698", "Context at depth 12, code 354330, node 1224698",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354330 and original node 1224698, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88601-1226280", "context_11_88601_1226280", "Context at depth 11, code 88601, node 1226280",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88601 and original node 1226280, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
