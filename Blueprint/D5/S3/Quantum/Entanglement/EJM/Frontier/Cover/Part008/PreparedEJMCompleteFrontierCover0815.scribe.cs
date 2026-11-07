using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0815Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0815.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0815",
        H("Original frontier context coverage 0815"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39124", "selected_cut_39124", "Selected cut at depth 13, code 1210426, node 1059903",
                "At remaining fuel 8 and original index 1059903, selection on the full partial prefix of depth 13 and code 1210426 returns the complete row with depth 13, base-four code 1210426, original node 1059903, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39170", "selected_cut_39170", "Selected cut at depth 12, code 302639, node 1061703",
                "At remaining fuel 9 and original index 1061703, selection on the full partial prefix of depth 12 and code 302639 returns the complete row with depth 12, base-four code 302639, original node 1061703, kind 2, reserved field 0, 3637 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-302606-1059914", "unmarked_context_12_302606_1059914", "Unmarked parent at depth 12, code 302606",
                "The frontier Boolean is false at remaining fuel 9, original node 1059914, the whole prefixCache at depth 12 and code 302606, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18914-1061705", "unmarked_context_10_18914_1061705", "Unmarked parent at depth 10, code 18914",
                "The frontier Boolean is false at remaining fuel 11, original node 1061705, the whole prefixCache at depth 10 and code 18914, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-302606-1059914", "node_context_12_302606_1059914", "Original split at fuel 9 and node 1059914",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1059869, 1059888, 1059903, 1059913. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18914-1061705", "node_context_10_18914_1061705", "Original split at fuel 11 and node 1061705",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1061057, 1061298, 1061479, 1061704. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1210426-1059903", "context_13_1210426_1059903", "Context at depth 13, code 1210426, node 1059903",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1210426 and original node 1059903, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-18914-1061705", "context_10_18914_1061705", "Context at depth 10, code 18914, node 1061705",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18914 and original node 1061705, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_75656_1061057, context_11_75657_1061298, context_11_75658_1061479, context_11_75659_1061704.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
