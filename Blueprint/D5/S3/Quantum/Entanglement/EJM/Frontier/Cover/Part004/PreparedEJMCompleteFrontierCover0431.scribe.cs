using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0431Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0431.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0431",
        H("Original frontier context coverage 0431"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20691", "selected_cut_20691", "Selected cut at depth 12, code 74112, node 530061",
                "At remaining fuel 9 and original index 530061, selection on the full partial prefix of depth 12 and code 74112 returns the complete row with depth 12, base-four code 74112, original node 530061, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20738", "selected_cut_20738", "Selected cut at depth 12, code 74159, node 531057",
                "At remaining fuel 9 and original index 531057, selection on the full partial prefix of depth 12 and code 74159 returns the complete row with depth 12, base-four code 74159, original node 531057, kind 2, reserved field 0, 1341 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-4631-530059", "unmarked_context_10_4631_530059", "Unmarked parent at depth 10, code 4631",
                "The frontier Boolean is false at remaining fuel 11, original node 530059, the whole prefixCache at depth 10 and code 4631, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18539-531058", "unmarked_context_11_18539_531058", "Unmarked parent at depth 11, code 18539",
                "The frontier Boolean is false at remaining fuel 10, original node 531058, the whole prefixCache at depth 11 and code 18539, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-4631-530059", "node_context_10_4631_530059", "Original split at fuel 11 and node 530059",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 529647, 529752, 529929, 530058. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18539-531058", "node_context_11_18539_531058", "Original split at fuel 10 and node 531058",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 531015, 531028, 531043, 531057. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-4631-530059", "context_10_4631_530059", "Context at depth 10, code 4631, node 530059",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4631 and original node 530059, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18524_529647, context_11_18525_529752, context_11_18526_529929, context_11_18527_530058.", DescribeRole.Theorem),
            Node("context-11-18539-531058", "context_11_18539_531058", "Context at depth 11, code 18539, node 531058",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18539 and original node 531058, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_74156_531015, context_12_74157_531028, context_12_74158_531043, context_12_74159_531057.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
