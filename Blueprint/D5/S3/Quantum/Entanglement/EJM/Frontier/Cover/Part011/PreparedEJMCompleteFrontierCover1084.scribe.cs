using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1084Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1084.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1084",
        H("Original frontier context coverage 1084"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52033", "selected_cut_52033", "Selected cut at depth 8, code 4480, node 1487329",
                "At remaining fuel 13 and original index 1487329, selection on the full partial prefix of depth 8 and code 4480 returns the complete row with depth 8, base-four code 4480, original node 1487329, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52081", "selected_cut_52081", "Selected cut at depth 10, code 71815, node 1511281",
                "At remaining fuel 11 and original index 1511281, selection on the full partial prefix of depth 10 and code 71815 returns the complete row with depth 10, base-four code 71815, original node 1511281, kind 2, reserved field 0, 889 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71713-1507977", "unmarked_context_10_71713_1507977", "Unmarked parent at depth 10, code 71713",
                "The frontier Boolean is false at remaining fuel 11, original node 1507977, the whole prefixCache at depth 10 and code 71713, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-17953-1511282", "unmarked_context_9_17953_1511282", "Unmarked parent at depth 9, code 17953",
                "The frontier Boolean is false at remaining fuel 12, original node 1511282, the whole prefixCache at depth 9 and code 17953, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71713-1507977", "node_context_10_71713_1507977", "Original split at fuel 11 and node 1507977",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1507607, 1468419, 1507806, 1507976. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-17953-1511282", "node_context_9_17953_1511282", "Original split at fuel 12 and node 1511282",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1511134, 1468874, 1511215, 1511281. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-4480-1487329", "context_8_4480_1487329", "Context at depth 8, code 4480, node 1487329",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 4480 and original node 1487329, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-17953-1511282", "context_9_17953_1511282", "Context at depth 9, code 17953, node 1511282",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17953 and original node 1511282, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_71812_1511134, context_10_71813_1468874, context_10_71814_1511215, context_10_71815_1511281.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
