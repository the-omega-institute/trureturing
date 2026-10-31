using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0532Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0532.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0532",
        H("Original frontier context coverage 0532"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25539", "selected_cut_25539", "Selected cut at depth 13, code 350385, node 646143",
                "At remaining fuel 8 and original index 646143, selection on the full partial prefix of depth 13 and code 350385 returns the complete row with depth 13, base-four code 350385, original node 646143, kind 2, reserved field 0, 1501 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25587", "selected_cut_25587", "Selected cut at depth 12, code 87663, node 648053",
                "At remaining fuel 9 and original index 648053, selection on the full partial prefix of depth 12 and code 87663 returns the complete row with depth 12, base-four code 87663, original node 648053, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-87596-646166", "unmarked_context_12_87596_646166", "Unmarked parent at depth 12, code 87596",
                "The frontier Boolean is false at remaining fuel 9, original node 646166, the whole prefixCache at depth 12 and code 87596, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-21914-647937", "unmarked_context_11_21914_647937", "Unmarked parent at depth 11, code 21914",
                "The frontier Boolean is false at remaining fuel 10, original node 647937, the whole prefixCache at depth 11 and code 21914, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-87596-646166", "node_context_12_87596_646166", "Original split at fuel 9 and node 646166",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 646124, 646143, 646159, 646165. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-21914-647937", "node_context_11_21914_647937", "Original split at fuel 10 and node 647937",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 647857, 647906, 445248, 647936. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-350385-646143", "context_13_350385_646143", "Context at depth 13, code 350385, node 646143",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 350385 and original node 646143, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-87663-648053", "context_12_87663_648053", "Context at depth 12, code 87663, node 648053",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 87663 and original node 648053, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
