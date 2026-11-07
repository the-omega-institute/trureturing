using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0616Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0616.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0616",
        H("Original frontier context coverage 0616"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29572", "selected_cut_29572", "Selected cut at depth 13, code 374812, node 746368",
                "At remaining fuel 8 and original index 746368, selection on the full partial prefix of depth 13 and code 374812 returns the complete row with depth 13, base-four code 374812, original node 746368, kind 2, reserved field 0, 4025 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29618", "selected_cut_29618", "Selected cut at depth 13, code 374867, node 747969",
                "At remaining fuel 8 and original index 747969, selection on the full partial prefix of depth 13 and code 374867 returns the complete row with depth 13, base-four code 374867, original node 747969, kind 2, reserved field 0, 917 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93702-746266", "unmarked_context_12_93702_746266", "Unmarked parent at depth 12, code 93702",
                "The frontier Boolean is false at remaining fuel 9, original node 746266, the whole prefixCache at depth 12 and code 93702, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93716-747970", "unmarked_context_12_93716_747970", "Unmarked parent at depth 12, code 93716",
                "The frontier Boolean is false at remaining fuel 9, original node 747970, the whole prefixCache at depth 12 and code 93716, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93702-746266", "node_context_12_93702_746266", "Original split at fuel 9 and node 746266",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 746181, 746234, 746255, 746265. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93716-747970", "node_context_12_93716_747970", "Original split at fuel 9 and node 747970",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 747905, 747941, 747962, 747969. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93702-746266", "context_12_93702_746266", "Context at depth 12, code 93702, node 746266",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93702 and original node 746266, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_374808_746181, context_13_374809_746234, context_13_374810_746255, context_13_374811_746265.", DescribeRole.Theorem),
            Node("context-12-93716-747970", "context_12_93716_747970", "Context at depth 12, code 93716, node 747970",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93716 and original node 747970, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_374864_747905, context_13_374865_747941, context_13_374866_747962, context_13_374867_747969.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
