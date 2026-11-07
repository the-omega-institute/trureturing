using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0963Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0963.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0963",
        H("Original frontier context coverage 0963"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46227", "selected_cut_46227", "Selected cut at depth 12, code 370188, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 370188 returns the complete row with depth 12, base-four code 370188, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46274", "selected_cut_46274", "Selected cut at depth 12, code 370244, node 1289585",
                "At remaining fuel 9 and original index 1289585, selection on the full partial prefix of depth 12 and code 370244 returns the complete row with depth 12, base-four code 370244, original node 1289585, kind 2, reserved field 0, 1969 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92547-1287952", "unmarked_context_11_92547_1287952", "Unmarked parent at depth 11, code 92547",
                "The frontier Boolean is false at remaining fuel 10, original node 1287952, the whole prefixCache at depth 11 and code 92547, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5784-1289529", "unmarked_context_9_5784_1289529", "Unmarked parent at depth 9, code 5784",
                "The frontier Boolean is false at remaining fuel 12, original node 1289529, the whole prefixCache at depth 9 and code 5784, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92547-1287952", "node_context_11_92547_1287952", "Original split at fuel 10 and node 1287952",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1287807, 1287874, 1287951. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5784-1289529", "node_context_9_5784_1289529", "Original split at fuel 12 and node 1289529",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1287953, 1288433, 1288990, 1289528. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-370188-448748", "context_12_370188_448748", "Context at depth 12, code 370188, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370188 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-370244-1289585", "context_12_370244_1289585", "Context at depth 12, code 370244, node 1289585",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370244 and original node 1289585, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
