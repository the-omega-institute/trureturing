using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0357Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0357.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0357",
        H("Original frontier context coverage 0357"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17138", "selected_cut_17138", "Selected cut at depth 13, code 278627, node 435581",
                "At remaining fuel 8 and original index 435581, selection on the full partial prefix of depth 13 and code 278627 returns the complete row with depth 13, base-four code 278627, original node 435581, kind 2, reserved field 0, 789 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17185", "selected_cut_17185", "Selected cut at depth 12, code 69718, node 436955",
                "At remaining fuel 9 and original index 436955, selection on the full partial prefix of depth 12 and code 69718 returns the complete row with depth 12, base-four code 69718, original node 436955, kind 2, reserved field 0, 3821 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-69656-435582", "unmarked_context_12_69656_435582", "Unmarked parent at depth 12, code 69656",
                "The frontier Boolean is false at remaining fuel 9, original node 435582, the whole prefixCache at depth 12 and code 69656, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17428-436856", "unmarked_context_11_17428_436856", "Unmarked parent at depth 11, code 17428",
                "The frontier Boolean is false at remaining fuel 10, original node 436856, the whole prefixCache at depth 11 and code 17428, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-69656-435582", "node_context_12_69656_435582", "Original split at fuel 9 and node 435582",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 435503, 435542, 435575, 435581. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17428-436856", "node_context_11_17428_436856", "Original split at fuel 10 and node 436856",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 436749, 436792, 436855, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-278627-435581", "context_13_278627_435581", "Context at depth 13, code 278627, node 435581",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 278627 and original node 435581, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-69718-436955", "context_12_69718_436955", "Context at depth 12, code 69718, node 436955",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 69718 and original node 436955, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
