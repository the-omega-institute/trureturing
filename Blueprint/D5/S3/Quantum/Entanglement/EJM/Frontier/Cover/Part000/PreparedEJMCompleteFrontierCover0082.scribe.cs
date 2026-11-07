using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0082Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0082.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0082",
        H("Original frontier context coverage 0082"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03939", "selected_cut_03939", "Selected cut at depth 13, code 70824, node 125819",
                "At remaining fuel 8 and original index 125819, selection on the full partial prefix of depth 13 and code 70824 returns the complete row with depth 13, base-four code 70824, original node 125819, kind 2, reserved field 0, 681 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03985", "selected_cut_03985", "Selected cut at depth 10, code 1111, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 1111 returns the complete row with depth 10, base-four code 1111, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17705-125798", "unmarked_context_12_17705_125798", "Unmarked parent at depth 12, code 17705",
                "The frontier Boolean is false at remaining fuel 9, original node 125798, the whole prefixCache at depth 12 and code 17705, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1110-127335", "unmarked_context_10_1110_127335", "Unmarked parent at depth 10, code 1110",
                "The frontier Boolean is false at remaining fuel 11, original node 127335, the whole prefixCache at depth 10 and code 1110, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17705-125798", "node_context_12_17705_125798", "Original split at fuel 9 and node 125798",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 125737, 125764, 125786, 125797. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1110-127335", "node_context_10_1110_127335", "Original split at fuel 11 and node 127335",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 126835, 126985, 127185, 127334. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-17705-125798", "context_12_17705_125798", "Context at depth 12, code 17705, node 125798",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 17705 and original node 125798, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_70820_125737, context_13_70821_125764, context_13_70822_125786, context_13_70823_125797.", DescribeRole.Theorem),
            Node("context-10-1111-3440", "context_10_1111_3440", "Context at depth 10, code 1111, node 3440",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1111 and original node 3440, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
