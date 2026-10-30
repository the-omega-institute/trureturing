using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0671Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0671.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0671",
        H("Original frontier context coverage 0671"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32211", "selected_cut_32211", "Selected cut at depth 12, code 107877, node 688903",
                "At remaining fuel 9 and original index 688903, selection on the full partial prefix of depth 12 and code 107877 returns the complete row with depth 12, base-four code 107877, original node 688903, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32259", "selected_cut_32259", "Selected cut at depth 12, code 107931, node 829016",
                "At remaining fuel 9 and original index 829016, selection on the full partial prefix of depth 12 and code 107931 returns the complete row with depth 12, base-four code 107931, original node 829016, kind 2, reserved field 0, 1717 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26969-827491", "unmarked_context_11_26969_827491", "Unmarked parent at depth 11, code 26969",
                "The frontier Boolean is false at remaining fuel 10, original node 827491, the whole prefixCache at depth 11 and code 26969, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26980-828957", "unmarked_context_11_26980_828957", "Unmarked parent at depth 11, code 26980",
                "The frontier Boolean is false at remaining fuel 10, original node 828957, the whole prefixCache at depth 11 and code 26980, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26969-827491", "node_context_11_26969_827491", "Original split at fuel 10 and node 827491",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 827378, 688903, 827426, 827490. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26980-828957", "node_context_11_26980_828957", "Original split at fuel 10 and node 828957",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 828869, 828888, 828934, 828956. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-107877-688903", "context_12_107877_688903", "Context at depth 12, code 107877, node 688903",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107877 and original node 688903, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-107931-829016", "context_12_107931_829016", "Context at depth 12, code 107931, node 829016",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107931 and original node 829016, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
