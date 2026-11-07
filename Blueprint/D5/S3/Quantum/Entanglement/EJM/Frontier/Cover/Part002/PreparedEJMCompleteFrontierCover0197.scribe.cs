using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0197Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0197.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0197",
        H("Original frontier context coverage 0197"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09460", "selected_cut_09460", "Selected cut at depth 12, code 23392, node 260853",
                "At remaining fuel 9 and original index 260853, selection on the full partial prefix of depth 12 and code 23392 returns the complete row with depth 12, base-four code 23392, original node 260853, kind 2, reserved field 0, 3941 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09506", "selected_cut_09506", "Selected cut at depth 12, code 23408, node 262154",
                "At remaining fuel 9 and original index 262154, selection on the full partial prefix of depth 12 and code 23408 returns the complete row with depth 12, base-four code 23408, original node 262154, kind 2, reserved field 0, 3165 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5847-260810", "unmarked_context_11_5847_260810", "Unmarked parent at depth 11, code 5847",
                "The frontier Boolean is false at remaining fuel 10, original node 260810, the whole prefixCache at depth 11 and code 5847, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1462-262110", "unmarked_context_10_1462_262110", "Unmarked parent at depth 10, code 1462",
                "The frontier Boolean is false at remaining fuel 11, original node 262110, the whole prefixCache at depth 10 and code 1462, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5847-260810", "node_context_11_5847_260810", "Original split at fuel 10 and node 260810",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 260500, 260591, 260656, 260809. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1462-262110", "node_context_10_1462_262110", "Original split at fuel 11 and node 262110",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 261062, 261283, 261809, 262109. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5847-260810", "context_11_5847_260810", "Context at depth 11, code 5847, node 260810",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5847 and original node 260810, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_23388_260500, context_12_23389_260591, context_12_23390_260656, context_12_23391_260809.", DescribeRole.Theorem),
            Node("context-12-23408-262154", "context_12_23408_262154", "Context at depth 12, code 23408, node 262154",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23408 and original node 262154, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
