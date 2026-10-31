using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1016Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1016.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1016",
        H("Original frontier context coverage 1016"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48772", "selected_cut_48772", "Selected cut at depth 12, code 403228, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 403228 returns the complete row with depth 12, base-four code 403228, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48818", "selected_cut_48818", "Selected cut at depth 11, code 100835, node 1373167",
                "At remaining fuel 10 and original index 1373167, selection on the full partial prefix of depth 11 and code 100835 returns the complete row with depth 11, base-four code 100835, original node 1373167, kind 2, reserved field 0, 1677 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-100806-1371312", "unmarked_context_11_100806_1371312", "Unmarked parent at depth 11, code 100806",
                "The frontier Boolean is false at remaining fuel 10, original node 1371312, the whole prefixCache at depth 11 and code 100806, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25208-1373168", "unmarked_context_10_25208_1373168", "Unmarked parent at depth 10, code 25208",
                "The frontier Boolean is false at remaining fuel 11, original node 1373168, the whole prefixCache at depth 10 and code 25208, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-100806-1371312", "node_context_11_100806_1371312", "Original split at fuel 10 and node 1371312",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1371219, 1371268, 1371311. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25208-1373168", "node_context_10_25208_1373168", "Original split at fuel 11 and node 1373168",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1373030, 1373080, 1373130, 1373167. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-100806-1371312", "context_11_100806_1371312", "Context at depth 11, code 100806, node 1371312",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 100806 and original node 1371312, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_403224_1108174, context_12_403225_1371219, context_12_403226_1371268, context_12_403227_1371311.", DescribeRole.Theorem),
            Node("context-10-25208-1373168", "context_10_25208_1373168", "Context at depth 10, code 25208, node 1373168",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25208 and original node 1373168, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_100832_1373030, context_11_100833_1373080, context_11_100834_1373130, context_11_100835_1373167.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
