using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0200Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0200.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0200",
        H("Original frontier context coverage 0200"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09602", "selected_cut_09602", "Selected cut at depth 7, code 23, node 34032",
                "At remaining fuel 14 and original index 34032, selection on the full partial prefix of depth 7 and code 23 returns the complete row with depth 7, base-four code 23, original node 34032, kind 1, reserved field 0, 1 subtree occurrences and completion domain 67108864. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09649", "selected_cut_09649", "Selected cut at depth 12, code 24595, node 266307",
                "At remaining fuel 9 and original index 266307, selection on the full partial prefix of depth 12 and code 24595 returns the complete row with depth 12, base-four code 24595, original node 266307, kind 2, reserved field 0, 3237 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-7-22-265057", "unmarked_context_7_22_265057", "Unmarked parent at depth 7, code 22",
                "The frontier Boolean is false at remaining fuel 14, original node 265057, the whole prefixCache at depth 7 and code 22, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1536-266169", "unmarked_context_10_1536_266169", "Unmarked parent at depth 10, code 1536",
                "The frontier Boolean is false at remaining fuel 11, original node 266169, the whole prefixCache at depth 10 and code 1536, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-7-22-265057", "node_context_7_22_265057", "Original split at fuel 14 and node 265057",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 225090, 235681, 249816, 265056. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1536-266169", "node_context_10_1536_266169", "Original split at fuel 11 and node 266169",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 167448, 265345, 265750, 266168. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-7-22-265057", "context_7_22_265057", "Context at depth 7, code 22, node 265057",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 22 and original node 265057, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_8_88_225090, context_8_89_235681, context_8_90_249816, context_8_91_265056.", DescribeRole.Theorem),
            Node("context-12-24595-266307", "context_12_24595_266307", "Context at depth 12, code 24595, node 266307",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 24595 and original node 266307, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
