using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0344Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0344.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0344",
        H("Original frontier context coverage 0344"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16516", "selected_cut_16516", "Selected cut at depth 12, code 28279, node 419982",
                "At remaining fuel 9 and original index 419982, selection on the full partial prefix of depth 12 and code 28279 returns the complete row with depth 12, base-four code 28279, original node 419982, kind 2, reserved field 0, 3549 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16563", "selected_cut_16563", "Selected cut at depth 12, code 28323, node 421330",
                "At remaining fuel 9 and original index 421330, selection on the full partial prefix of depth 12 and code 28323 returns the complete row with depth 12, base-four code 28323, original node 421330, kind 2, reserved field 0, 1881 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7069-419983", "unmarked_context_11_7069_419983", "Unmarked parent at depth 11, code 7069",
                "The frontier Boolean is false at remaining fuel 10, original node 419983, the whole prefixCache at depth 11 and code 7069, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1769-421249", "unmarked_context_10_1769_421249", "Unmarked parent at depth 10, code 1769",
                "The frontier Boolean is false at remaining fuel 11, original node 421249, the whole prefixCache at depth 10 and code 1769, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7069-419983", "node_context_11_7069_419983", "Original split at fuel 10 and node 419983",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 419797, 419904, 419938, 419982. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1769-421249", "node_context_10_1769_421249", "Original split at fuel 11 and node 421249",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 421025, 421114, 421175, 421248. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-28279-419982", "context_12_28279_419982", "Context at depth 12, code 28279, node 419982",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28279 and original node 419982, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-28323-421330", "context_12_28323_421330", "Context at depth 12, code 28323, node 421330",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28323 and original node 421330, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
