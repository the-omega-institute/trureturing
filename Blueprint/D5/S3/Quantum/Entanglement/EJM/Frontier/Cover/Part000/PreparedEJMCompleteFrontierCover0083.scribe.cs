using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0083Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0083.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0083",
        H("Original frontier context coverage 0083"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03986", "selected_cut_03986", "Selected cut at depth 10, code 1112, node 3442",
                "At remaining fuel 11 and original index 3442, selection on the full partial prefix of depth 10 and code 1112 returns the complete row with depth 10, base-four code 1112, original node 3442, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04033", "selected_cut_04033", "Selected cut at depth 12, code 17929, node 895",
                "At remaining fuel 9 and original index 895, selection on the full partial prefix of depth 12 and code 17929 returns the complete row with depth 12, base-four code 17929, original node 895, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-277-127336", "unmarked_context_9_277_127336", "Unmarked parent at depth 9, code 277",
                "The frontier Boolean is false at remaining fuel 12, original node 127336, the whole prefixCache at depth 9 and code 277, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4481-128570", "unmarked_context_11_4481_128570", "Unmarked parent at depth 11, code 4481",
                "The frontier Boolean is false at remaining fuel 10, original node 128570, the whole prefixCache at depth 11 and code 4481, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-277-127336", "node_context_9_277_127336", "Original split at fuel 12 and node 127336",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 3442, 126578, 127335, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4481-128570", "node_context_11_4481_128570", "Original split at fuel 10 and node 128570",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 128309, 128428, 128569. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-277-127336", "context_9_277_127336", "Context at depth 9, code 277, node 127336",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 277 and original node 127336, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1108_3442, context_10_1109_126578, context_10_1110_127335, context_10_1111_3440.", DescribeRole.Theorem),
            Node("context-12-17929-895", "context_12_17929_895", "Context at depth 12, code 17929, node 895",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 17929 and original node 895, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
