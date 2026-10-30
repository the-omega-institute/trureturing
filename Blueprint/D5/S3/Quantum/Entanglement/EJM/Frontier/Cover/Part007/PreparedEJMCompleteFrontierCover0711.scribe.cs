using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0711Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0711.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0711",
        H("Original frontier context coverage 0711"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34132", "selected_cut_34132", "Selected cut at depth 13, code 451828, node 881318",
                "At remaining fuel 8 and original index 881318, selection on the full partial prefix of depth 13 and code 451828 returns the complete row with depth 13, base-four code 451828, original node 881318, kind 2, reserved field 0, 97 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34179", "selected_cut_34179", "Selected cut at depth 12, code 113004, node 883082",
                "At remaining fuel 9 and original index 883082, selection on the full partial prefix of depth 12 and code 113004 returns the complete row with depth 12, base-four code 113004, original node 883082, kind 2, reserved field 0, 2617 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-112957-881371", "unmarked_context_12_112957_881371", "Unmarked parent at depth 12, code 112957",
                "The frontier Boolean is false at remaining fuel 9, original node 881371, the whole prefixCache at depth 12 and code 112957, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-28249-883047", "unmarked_context_11_28249_883047", "Unmarked parent at depth 11, code 28249",
                "The frontier Boolean is false at remaining fuel 10, original node 883047, the whole prefixCache at depth 11 and code 28249, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-112957-881371", "node_context_12_112957_881371", "Original split at fuel 9 and node 881371",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 881318, 881342, 881363, 881370. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-28249-883047", "node_context_11_28249_883047", "Original split at fuel 10 and node 883047",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 882979, 688903, 883016, 883046. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-451828-881318", "context_13_451828_881318", "Context at depth 13, code 451828, node 881318",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 451828 and original node 881318, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-113004-883082", "context_12_113004_883082", "Context at depth 12, code 113004, node 883082",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 113004 and original node 883082, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
