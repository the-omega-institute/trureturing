using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0802Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0802.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0802",
        H("Original frontier context coverage 0802"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38499", "selected_cut_38499", "Selected cut at depth 13, code 1206324, node 1038030",
                "At remaining fuel 8 and original index 1038030, selection on the full partial prefix of depth 13 and code 1206324 returns the complete row with depth 13, base-four code 1206324, original node 1038030, kind 2, reserved field 0, 1737 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38547", "selected_cut_38547", "Selected cut at depth 12, code 301623, node 1040142",
                "At remaining fuel 9 and original index 1040142, selection on the full partial prefix of depth 12 and code 301623 returns the complete row with depth 12, base-four code 301623, original node 1040142, kind 2, reserved field 0, 3301 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-301581-1038090", "unmarked_context_12_301581_1038090", "Unmarked parent at depth 12, code 301581",
                "The frontier Boolean is false at remaining fuel 9, original node 1038090, the whole prefixCache at depth 12 and code 301581, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75404-1039898", "unmarked_context_11_75404_1039898", "Unmarked parent at depth 11, code 75404",
                "The frontier Boolean is false at remaining fuel 10, original node 1039898, the whole prefixCache at depth 11 and code 75404, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-301581-1038090", "node_context_12_301581_1038090", "Original split at fuel 9 and node 1038090",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1038030, 1038053, 1038074, 1038089. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75404-1039898", "node_context_11_75404_1039898", "Original split at fuel 10 and node 1039898",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1039789, 1039837, 1039897. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1206324-1038030", "context_13_1206324_1038030", "Context at depth 13, code 1206324, node 1038030",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1206324 and original node 1038030, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301623-1040142", "context_12_301623_1040142", "Context at depth 12, code 301623, node 1040142",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301623 and original node 1040142, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
