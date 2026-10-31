using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0719Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0719.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0719",
        H("Original frontier context coverage 0719"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34515", "selected_cut_34515", "Selected cut at depth 10, code 17508, node 3442",
                "At remaining fuel 11 and original index 3442, selection on the full partial prefix of depth 10 and code 17508 returns the complete row with depth 10, base-four code 17508, original node 3442, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34562", "selected_cut_34562", "Selected cut at depth 13, code 1124381, node 898578",
                "At remaining fuel 8 and original index 898578, selection on the full partial prefix of depth 13 and code 1124381 returns the complete row with depth 13, base-four code 1124381, original node 898578, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17507-896641", "unmarked_context_10_17507_896641", "Unmarked parent at depth 10, code 17507",
                "The frontier Boolean is false at remaining fuel 11, original node 896641, the whole prefixCache at depth 10 and code 17507, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-281094-898503", "unmarked_context_12_281094_898503", "Unmarked parent at depth 12, code 281094",
                "The frontier Boolean is false at remaining fuel 9, original node 898503, the whole prefixCache at depth 12 and code 281094, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17507-896641", "node_context_10_17507_896641", "Original split at fuel 11 and node 896641",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 896152, 896342, 896480, 896640. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-281094-898503", "node_context_12_281094_898503", "Original split at fuel 9 and node 898503",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 898425, 898454, 898490, 898502. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-17507-896641", "context_10_17507_896641", "Context at depth 10, code 17507, node 896641",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17507 and original node 896641, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_70028_896152, context_11_70029_896342, context_11_70030_896480, context_11_70031_896640.", DescribeRole.Theorem),
            Node("context-13-1124381-898578", "context_13_1124381_898578", "Context at depth 13, code 1124381, node 898578",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1124381 and original node 898578, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
