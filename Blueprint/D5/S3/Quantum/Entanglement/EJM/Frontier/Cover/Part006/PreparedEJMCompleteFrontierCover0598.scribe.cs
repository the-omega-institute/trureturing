using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0598Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0598.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0598",
        H("Original frontier context coverage 0598"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28707", "selected_cut_28707", "Selected cut at depth 13, code 371781, node 724062",
                "At remaining fuel 8 and original index 724062, selection on the full partial prefix of depth 13 and code 371781 returns the complete row with depth 13, base-four code 371781, original node 724062, kind 2, reserved field 0, 1605 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28755", "selected_cut_28755", "Selected cut at depth 13, code 371829, node 725021",
                "At remaining fuel 8 and original index 725021, selection on the full partial prefix of depth 13 and code 371829 returns the complete row with depth 13, base-four code 371829, original node 725021, kind 2, reserved field 0, 1453 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92945-724088", "unmarked_context_12_92945_724088", "Unmarked parent at depth 12, code 92945",
                "The frontier Boolean is false at remaining fuel 9, original node 724088, the whole prefixCache at depth 12 and code 92945, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92956-724975", "unmarked_context_12_92956_724975", "Unmarked parent at depth 12, code 92956",
                "The frontier Boolean is false at remaining fuel 9, original node 724975, the whole prefixCache at depth 12 and code 92956, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92945-724088", "node_context_12_92945_724088", "Original split at fuel 9 and node 724088",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 724035, 724062, 724081, 724087. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92956-724975", "node_context_12_92956_724975", "Original split at fuel 9 and node 724975",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 724923, 724953, 724968, 724974. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-371781-724062", "context_13_371781_724062", "Context at depth 13, code 371781, node 724062",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 371781 and original node 724062, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-371829-725021", "context_13_371829_725021", "Context at depth 13, code 371829, node 725021",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 371829 and original node 725021, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
