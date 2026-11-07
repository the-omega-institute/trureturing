using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0852Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0852.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0852",
        H("Original frontier context coverage 0852"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40899", "selected_cut_40899", "Selected cut at depth 12, code 333360, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 333360 returns the complete row with depth 12, base-four code 333360, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40947", "selected_cut_40947", "Selected cut at depth 12, code 333423, node 1117223",
                "At remaining fuel 9 and original index 1117223, selection on the full partial prefix of depth 12 and code 333423 returns the complete row with depth 12, base-four code 333423, original node 1117223, kind 2, reserved field 0, 1909 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-20834-1115801", "unmarked_context_10_20834_1115801", "Unmarked parent at depth 10, code 20834",
                "The frontier Boolean is false at remaining fuel 11, original node 1115801, the whole prefixCache at depth 10 and code 20834, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83354-1117100", "unmarked_context_11_83354_1117100", "Unmarked parent at depth 11, code 83354",
                "The frontier Boolean is false at remaining fuel 10, original node 1117100, the whole prefixCache at depth 11 and code 83354, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-20834-1115801", "node_context_10_20834_1115801", "Original split at fuel 11 and node 1115801",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1115450, 1115589, 1115682, 1115800. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83354-1117100", "node_context_11_83354_1117100", "Original split at fuel 10 and node 1117100",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1117009, 1117057, 1113261, 1117099. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-20834-1115801", "context_10_20834_1115801", "Context at depth 10, code 20834, node 1115801",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 20834 and original node 1115801, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_83336_1115450, context_11_83337_1115589, context_11_83338_1115682, context_11_83339_1115800.", DescribeRole.Theorem),
            Node("context-12-333423-1117223", "context_12_333423_1117223", "Context at depth 12, code 333423, node 1117223",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 333423 and original node 1117223, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
