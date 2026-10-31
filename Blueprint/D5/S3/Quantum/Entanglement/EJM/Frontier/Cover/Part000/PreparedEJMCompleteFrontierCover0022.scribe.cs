using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0022Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0022.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0022",
        H("Original frontier context coverage 0022"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01057", "selected_cut_01057", "Selected cut at depth 12, code 4372, node 41832",
                "At remaining fuel 9 and original index 41832, selection on the full partial prefix of depth 12 and code 4372 returns the complete row with depth 12, base-four code 4372, original node 41832, kind 2, reserved field 0, 3945 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01105", "selected_cut_01105", "Selected cut at depth 13, code 17557, node 43131",
                "At remaining fuel 8 and original index 43131, selection on the full partial prefix of depth 13 and code 17557 returns the complete row with depth 13, base-four code 17557, original node 43131, kind 2, reserved field 0, 3769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4373-41921", "unmarked_context_12_4373_41921", "Unmarked parent at depth 12, code 4373",
                "The frontier Boolean is false at remaining fuel 9, original node 41921, the whole prefixCache at depth 12 and code 4373, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4388-43055", "unmarked_context_12_4388_43055", "Unmarked parent at depth 12, code 4388",
                "The frontier Boolean is false at remaining fuel 9, original node 43055, the whole prefixCache at depth 12 and code 4388, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4373-41921", "node_context_12_4373_41921", "Original split at fuel 9 and node 41921",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 41861, 41891, 41920, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4388-43055", "node_context_12_4388_43055", "Original split at fuel 9 and node 43055",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 42964, 43005, 43034, 43054. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4372-41832", "context_12_4372_41832", "Context at depth 12, code 4372, node 41832",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4372 and original node 41832, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-17557-43131", "context_13_17557_43131", "Context at depth 13, code 17557, node 43131",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17557 and original node 43131, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
