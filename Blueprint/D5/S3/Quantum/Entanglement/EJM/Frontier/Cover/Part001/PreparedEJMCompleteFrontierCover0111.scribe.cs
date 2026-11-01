using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0111Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0111.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0111",
        H("Original frontier context coverage 0111"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05331", "selected_cut_05331", "Selected cut at depth 13, code 77145, node 165117",
                "At remaining fuel 8 and original index 165117, selection on the full partial prefix of depth 13 and code 77145 returns the complete row with depth 13, base-four code 77145, original node 165117, kind 2, reserved field 0, 2313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05377", "selected_cut_05377", "Selected cut at depth 12, code 19327, node 167002",
                "At remaining fuel 9 and original index 167002, selection on the full partial prefix of depth 12 and code 19327 returns the complete row with depth 12, base-four code 19327, original node 167002, kind 2, reserved field 0, 1569 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-19286-165151", "unmarked_context_12_19286_165151", "Unmarked parent at depth 12, code 19286",
                "The frontier Boolean is false at remaining fuel 9, original node 165151, the whole prefixCache at depth 12 and code 19286, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-301-167005", "unmarked_context_9_301_167005", "Unmarked parent at depth 9, code 301",
                "The frontier Boolean is false at remaining fuel 12, original node 167005, the whole prefixCache at depth 9 and code 301, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-19286-165151", "node_context_12_19286_165151", "Original split at fuel 9 and node 165151",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 165117, 165142, 165150. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-301-167005", "node_context_9_301_167005", "Original split at fuel 12 and node 167005",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 145424, 165783, 166433, 167004. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-77145-165117", "context_13_77145_165117", "Context at depth 13, code 77145, node 165117",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 77145 and original node 165117, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-301-167005", "context_9_301_167005", "Context at depth 9, code 301, node 167005",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 301 and original node 167005, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1204_145424, context_10_1205_165783, context_10_1206_166433, context_10_1207_167004.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
