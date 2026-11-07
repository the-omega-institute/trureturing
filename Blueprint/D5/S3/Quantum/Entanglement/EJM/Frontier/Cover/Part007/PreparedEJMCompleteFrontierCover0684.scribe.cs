using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0684Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0684.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0684",
        H("Original frontier context coverage 0684"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32835", "selected_cut_32835", "Selected cut at depth 13, code 439362, node 845554",
                "At remaining fuel 8 and original index 845554, selection on the full partial prefix of depth 13 and code 439362 returns the complete row with depth 13, base-four code 439362, original node 845554, kind 2, reserved field 0, 1161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32883", "selected_cut_32883", "Selected cut at depth 13, code 439413, node 846746",
                "At remaining fuel 8 and original index 846746, selection on the full partial prefix of depth 13 and code 439413 returns the complete row with depth 13, base-four code 439413, original node 846746, kind 2, reserved field 0, 2521 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109840-845562", "unmarked_context_12_109840_845562", "Unmarked parent at depth 12, code 109840",
                "The frontier Boolean is false at remaining fuel 9, original node 845562, the whole prefixCache at depth 12 and code 109840, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109852-846690", "unmarked_context_12_109852_846690", "Unmarked parent at depth 12, code 109852",
                "The frontier Boolean is false at remaining fuel 9, original node 846690, the whole prefixCache at depth 12 and code 109852, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109840-845562", "node_context_12_109840_845562", "Original split at fuel 9 and node 845562",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 845508, 845532, 845554, 845561. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109852-846690", "node_context_12_109852_846690", "Original split at fuel 9 and node 846690",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 846633, 846663, 846682, 846689. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-439362-845554", "context_13_439362_845554", "Context at depth 13, code 439362, node 845554",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439362 and original node 845554, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-439413-846746", "context_13_439413_846746", "Context at depth 13, code 439413, node 846746",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439413 and original node 846746, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
