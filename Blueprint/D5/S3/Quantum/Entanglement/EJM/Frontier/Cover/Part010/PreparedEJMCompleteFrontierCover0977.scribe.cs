using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0977Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0977.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0977",
        H("Original frontier context coverage 0977"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46900", "selected_cut_46900", "Selected cut at depth 12, code 371815, node 1309804",
                "At remaining fuel 9 and original index 1309804, selection on the full partial prefix of depth 12 and code 371815 returns the complete row with depth 12, base-four code 371815, original node 1309804, kind 2, reserved field 0, 1717 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46947", "selected_cut_46947", "Selected cut at depth 12, code 371991, node 692794",
                "At remaining fuel 9 and original index 692794, selection on the full partial prefix of depth 12 and code 371991 returns the complete row with depth 12, base-four code 371991, original node 692794, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92953-1309805", "unmarked_context_11_92953_1309805", "Unmarked parent at depth 11, code 92953",
                "The frontier Boolean is false at remaining fuel 10, original node 1309805, the whole prefixCache at depth 11 and code 92953, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92996-1311602", "unmarked_context_11_92996_1311602", "Unmarked parent at depth 11, code 92996",
                "The frontier Boolean is false at remaining fuel 10, original node 1311602, the whole prefixCache at depth 11 and code 92996, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92953-1309805", "node_context_11_92953_1309805", "Original split at fuel 10 and node 1309805",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1309735, 1256866, 1309764, 1309804. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92996-1311602", "node_context_11_92996_1311602", "Original split at fuel 10 and node 1311602",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 789343, 1311504, 1311547, 1311601. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-371815-1309804", "context_12_371815_1309804", "Context at depth 12, code 371815, node 1309804",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371815 and original node 1309804, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-371991-692794", "context_12_371991_692794", "Context at depth 12, code 371991, node 692794",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371991 and original node 692794, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
