using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0112Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0112.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0112",
        H("Original frontier context coverage 0112"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05378", "selected_cut_05378", "Selected cut at depth 10, code 1208, node 145424",
                "At remaining fuel 11 and original index 145424, selection on the full partial prefix of depth 10 and code 1208 returns the complete row with depth 10, base-four code 1208, original node 145424, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05425", "selected_cut_05425", "Selected cut at depth 12, code 20503, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 20503 returns the complete row with depth 12, base-four code 20503, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1209-167217", "unmarked_context_10_1209_167217", "Unmarked parent at depth 10, code 1209",
                "The frontier Boolean is false at remaining fuel 11, original node 167217, the whole prefixCache at depth 10 and code 1209, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-20502-168522", "unmarked_context_12_20502_168522", "Unmarked parent at depth 12, code 20502",
                "The frontier Boolean is false at remaining fuel 9, original node 168522, the whole prefixCache at depth 12 and code 20502, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1209-167217", "node_context_10_1209_167217", "Original split at fuel 11 and node 167217",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 167105, 167168, 167201, 167216. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-20502-168522", "node_context_12_20502_168522", "Original split at fuel 9 and node 168522",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 168468, 168499, 168518, 168521. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1208-145424", "context_10_1208_145424", "Context at depth 10, code 1208, node 145424",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1208 and original node 145424, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-20503-893", "context_12_20503_893", "Context at depth 12, code 20503, node 893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20503 and original node 893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
