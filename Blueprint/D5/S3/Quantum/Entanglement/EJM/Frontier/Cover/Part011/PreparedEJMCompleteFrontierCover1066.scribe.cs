using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1066Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1066.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1066",
        H("Original frontier context coverage 1066"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51170", "selected_cut_51170", "Selected cut at depth 10, code 69716, node 1471943",
                "At remaining fuel 11 and original index 1471943, selection on the full partial prefix of depth 10 and code 69716 returns the complete row with depth 10, base-four code 69716, original node 1471943, kind 2, reserved field 0, 2213 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51217", "selected_cut_51217", "Selected cut at depth 12, code 1116691, node 1473783",
                "At remaining fuel 9 and original index 1473783, selection on the full partial prefix of depth 12 and code 1116691 returns the complete row with depth 12, base-four code 1116691, original node 1473783, kind 2, reserved field 0, 1657 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17428-1471851", "unmarked_context_9_17428_1471851", "Unmarked parent at depth 9, code 17428",
                "The frontier Boolean is false at remaining fuel 12, original node 1471851, the whole prefixCache at depth 9 and code 17428, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-279172-1473784", "unmarked_context_11_279172_1473784", "Unmarked parent at depth 11, code 279172",
                "The frontier Boolean is false at remaining fuel 10, original node 1473784, the whole prefixCache at depth 11 and code 279172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17428-1471851", "node_context_9_17428_1471851", "Original split at fuel 12 and node 1471851",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1471677, 1471850, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-279172-1473784", "node_context_11_279172_1473784", "Original split at fuel 10 and node 1473784",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1473679, 1473721, 1473783. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-17428-1471851", "context_9_17428_1471851", "Context at depth 9, code 17428, node 1471851",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17428 and original node 1471851, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_69712_1468246, context_10_69713_1471677, context_10_69714_1471850, context_10_69715_3440.", DescribeRole.Theorem),
            Node("context-11-279172-1473784", "context_11_279172_1473784", "Context at depth 11, code 279172, node 1473784",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 279172 and original node 1473784, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_1116688_1738, context_12_1116689_1473679, context_12_1116690_1473721, context_12_1116691_1473783.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
