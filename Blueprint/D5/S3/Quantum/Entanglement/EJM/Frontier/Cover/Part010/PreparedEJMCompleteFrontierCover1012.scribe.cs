using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1012Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1012.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1012",
        H("Original frontier context coverage 1012"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48580", "selected_cut_48580", "Selected cut at depth 12, code 376648, node 1363666",
                "At remaining fuel 9 and original index 1363666, selection on the full partial prefix of depth 12 and code 376648 returns the complete row with depth 12, base-four code 376648, original node 1363666, kind 2, reserved field 0, 1757 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48625", "selected_cut_48625", "Selected cut at depth 11, code 100423, node 1365012",
                "At remaining fuel 10 and original index 1365012, selection on the full partial prefix of depth 11 and code 100423 returns the complete row with depth 11, base-four code 100423, original node 1365012, kind 2, reserved field 0, 3049 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-94162-1363724", "unmarked_context_11_94162_1363724", "Unmarked parent at depth 11, code 94162",
                "The frontier Boolean is false at remaining fuel 10, original node 1363724, the whole prefixCache at depth 11 and code 94162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25105-1365013", "unmarked_context_10_25105_1365013", "Unmarked parent at depth 10, code 25105",
                "The frontier Boolean is false at remaining fuel 11, original node 1365013, the whole prefixCache at depth 10 and code 25105, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-94162-1363724", "node_context_11_94162_1363724", "Original split at fuel 10 and node 1363724",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1363666, 1025817, 1363695, 1363723. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25105-1365013", "node_context_10_25105_1365013", "Original split at fuel 11 and node 1365013",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1364850, 451541, 1364934, 1365012. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-376648-1363666", "context_12_376648_1363666", "Context at depth 12, code 376648, node 1363666",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 376648 and original node 1363666, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-25105-1365013", "context_10_25105_1365013", "Context at depth 10, code 25105, node 1365013",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25105 and original node 1365013, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_100420_1364850, context_11_100421_451541, context_11_100422_1364934, context_11_100423_1365012.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
