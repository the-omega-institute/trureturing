using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0836Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0836.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0836",
        H("Original frontier context coverage 0836"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40131", "selected_cut_40131", "Selected cut at depth 13, code 1234965, node 1089851",
                "At remaining fuel 8 and original index 1089851, selection on the full partial prefix of depth 13 and code 1234965 returns the complete row with depth 13, base-four code 1234965, original node 1089851, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40179", "selected_cut_40179", "Selected cut at depth 12, code 308766, node 1091011",
                "At remaining fuel 9 and original index 1091011, selection on the full partial prefix of depth 12 and code 308766 returns the complete row with depth 12, base-four code 308766, original node 1091011, kind 2, reserved field 0, 2249 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-308741-1089893", "unmarked_context_12_308741_1089893", "Unmarked parent at depth 12, code 308741",
                "The frontier Boolean is false at remaining fuel 9, original node 1089893, the whole prefixCache at depth 12 and code 308741, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77190-1090893", "unmarked_context_11_77190_1090893", "Unmarked parent at depth 11, code 77190",
                "The frontier Boolean is false at remaining fuel 10, original node 1090893, the whole prefixCache at depth 11 and code 77190, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-308741-1089893", "node_context_12_308741_1089893", "Original split at fuel 9 and node 1089893",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1089828, 1089851, 1089873, 1089892. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77190-1090893", "node_context_11_77190_1090893", "Original split at fuel 10 and node 1090893",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 26677, 1090826, 3161, 1090892. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1234965-1089851", "context_13_1234965_1089851", "Context at depth 13, code 1234965, node 1089851",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1234965 and original node 1089851, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-308766-1091011", "context_12_308766_1091011", "Context at depth 12, code 308766, node 1091011",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308766 and original node 1091011, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
