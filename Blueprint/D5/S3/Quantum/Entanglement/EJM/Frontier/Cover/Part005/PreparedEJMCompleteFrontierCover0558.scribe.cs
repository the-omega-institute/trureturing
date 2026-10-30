using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0558Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0558.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0558",
        H("Original frontier context coverage 0558"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26787", "selected_cut_26787", "Selected cut at depth 13, code 364575, node 676997",
                "At remaining fuel 8 and original index 676997, selection on the full partial prefix of depth 13 and code 364575 returns the complete row with depth 13, base-four code 364575, original node 676997, kind 2, reserved field 0, 145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26834", "selected_cut_26834", "Selected cut at depth 13, code 364634, node 678726",
                "At remaining fuel 8 and original index 678726, selection on the full partial prefix of depth 13 and code 364634 returns the complete row with depth 13, base-four code 364634, original node 678726, kind 2, reserved field 0, 1681 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91143-676998", "unmarked_context_12_91143_676998", "Unmarked parent at depth 12, code 91143",
                "The frontier Boolean is false at remaining fuel 9, original node 676998, the whole prefixCache at depth 12 and code 91143, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22788-678485", "unmarked_context_11_22788_678485", "Unmarked parent at depth 11, code 22788",
                "The frontier Boolean is false at remaining fuel 10, original node 678485, the whole prefixCache at depth 11 and code 22788, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91143-676998", "node_context_12_91143_676998", "Original split at fuel 9 and node 676998",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 676944, 676981, 676993, 676997. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22788-678485", "node_context_11_22788_678485", "Original split at fuel 10 and node 678485",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 307381, 678324, 678396, 678484. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-364575-676997", "context_13_364575_676997", "Context at depth 13, code 364575, node 676997",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 364575 and original node 676997, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-364634-678726", "context_13_364634_678726", "Context at depth 13, code 364634, node 678726",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 364634 and original node 678726, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
