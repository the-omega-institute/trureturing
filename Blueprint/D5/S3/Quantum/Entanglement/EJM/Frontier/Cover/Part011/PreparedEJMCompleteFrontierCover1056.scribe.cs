using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1056Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1056.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1056",
        H("Original frontier context coverage 1056"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50691", "selected_cut_50691", "Selected cut at depth 12, code 440592, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 440592 returns the complete row with depth 12, base-four code 440592, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50739", "selected_cut_50739", "Selected cut at depth 10, code 27549, node 1452715",
                "At remaining fuel 11 and original index 1452715, selection on the full partial prefix of depth 10 and code 27549 returns the complete row with depth 10, base-four code 27549, original node 1452715, kind 2, reserved field 0, 1361 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-110148-1450805", "unmarked_context_11_110148_1450805", "Unmarked parent at depth 11, code 110148",
                "The frontier Boolean is false at remaining fuel 10, original node 1450805, the whole prefixCache at depth 11 and code 110148, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6886-1452584", "unmarked_context_9_6886_1452584", "Unmarked parent at depth 9, code 6886",
                "The frontier Boolean is false at remaining fuel 12, original node 1452584, the whole prefixCache at depth 9 and code 6886, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-110148-1450805", "node_context_11_110148_1450805", "Original split at fuel 10 and node 1450805",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1450708, 1450760, 1450804. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6886-1452584", "node_context_9_6886_1452584", "Original split at fuel 12 and node 1452584",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1452430, 1452521, 1432895, 1452583. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-440592-435790", "context_12_440592_435790", "Context at depth 12, code 440592, node 435790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 440592 and original node 435790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-27549-1452715", "context_10_27549_1452715", "Context at depth 10, code 27549, node 1452715",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 27549 and original node 1452715, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
