using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0723Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0723.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0723",
        H("Original frontier context coverage 0723"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34707", "selected_cut_34707", "Selected cut at depth 12, code 281472, node 905706",
                "At remaining fuel 9 and original index 905706, selection on the full partial prefix of depth 12 and code 281472 returns the complete row with depth 12, base-four code 281472, original node 905706, kind 2, reserved field 0, 1653 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34753", "selected_cut_34753", "Selected cut at depth 12, code 282634, node 907186",
                "At remaining fuel 9 and original index 907186, selection on the full partial prefix of depth 12 and code 282634 returns the complete row with depth 12, base-four code 282634, original node 907186, kind 2, reserved field 0, 2813 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-4397-905682", "unmarked_context_9_4397_905682", "Unmarked parent at depth 9, code 4397",
                "The frontier Boolean is false at remaining fuel 12, original node 905682, the whole prefixCache at depth 9 and code 4397, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-70657-906965", "unmarked_context_11_70657_906965", "Unmarked parent at depth 11, code 70657",
                "The frontier Boolean is false at remaining fuel 10, original node 906965, the whole prefixCache at depth 11 and code 70657, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-4397-905682", "node_context_9_4397_905682", "Original split at fuel 12 and node 905682",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 905415, 893098, 905589, 905681. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-70657-906965", "node_context_11_70657_906965", "Original split at fuel 10 and node 906965",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 906842, 906879, 906964, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-4397-905682", "context_9_4397_905682", "Context at depth 9, code 4397, node 905682",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 4397 and original node 905682, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_17588_905415, context_10_17589_893098, context_10_17590_905589, context_10_17591_905681.", DescribeRole.Theorem),
            Node("context-12-282634-907186", "context_12_282634_907186", "Context at depth 12, code 282634, node 907186",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 282634 and original node 907186, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
