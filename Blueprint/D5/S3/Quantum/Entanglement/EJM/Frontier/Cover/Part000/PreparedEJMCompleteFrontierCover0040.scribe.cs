using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0040Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0040.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0040",
        H("Original frontier context coverage 0040"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01922", "selected_cut_01922", "Selected cut at depth 14, code 86051, node 63956",
                "At remaining fuel 7 and original index 63956, selection on the full partial prefix of depth 14 and code 86051 returns the complete row with depth 14, base-four code 86051, original node 63956, kind 2, reserved field 0, 1181 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01968", "selected_cut_01968", "Selected cut at depth 11, code 1347, node 1736",
                "At remaining fuel 10 and original index 1736, selection on the full partial prefix of depth 11 and code 1347 returns the complete row with depth 11, base-four code 1347, original node 1736, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-21512-63957", "unmarked_context_13_21512_63957", "Unmarked parent at depth 13, code 21512",
                "The frontier Boolean is false at remaining fuel 8, original node 63957, the whole prefixCache at depth 13 and code 21512, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-336-65686", "unmarked_context_10_336_65686", "Unmarked parent at depth 10, code 336",
                "The frontier Boolean is false at remaining fuel 11, original node 65686, the whole prefixCache at depth 10 and code 336, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-21512-63957", "node_context_13_21512_63957", "Original split at fuel 8 and node 63957",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 63889, 63910, 63935, 63956. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-336-65686", "node_context_10_336_65686", "Original split at fuel 11 and node 65686",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 64066, 64705, 65685, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-86051-63956", "context_14_86051_63956", "Context at depth 14, code 86051, node 63956",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 86051 and original node 63956, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-336-65686", "context_10_336_65686", "Context at depth 10, code 336, node 65686",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 336 and original node 65686, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_1344_64066, context_11_1345_64705, context_11_1346_65685, context_11_1347_1736.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
