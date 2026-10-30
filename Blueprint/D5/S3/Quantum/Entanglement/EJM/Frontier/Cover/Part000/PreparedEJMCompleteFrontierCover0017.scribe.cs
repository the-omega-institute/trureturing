using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0017Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0017.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0017",
        H("Original frontier context coverage 0017"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00818", "selected_cut_00818", "Selected cut at depth 12, code 1652, node 33059",
                "At remaining fuel 9 and original index 33059, selection on the full partial prefix of depth 12 and code 1652 returns the complete row with depth 12, base-four code 1652, original node 33059, kind 2, reserved field 0, 2189 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00865", "selected_cut_00865", "Selected cut at depth 13, code 16426, node 35093",
                "At remaining fuel 8 and original index 35093, selection on the full partial prefix of depth 13 and code 16426 returns the complete row with depth 13, base-four code 16426, original node 35093, kind 2, reserved field 0, 1729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-413-33207", "unmarked_context_11_413_33207", "Unmarked parent at depth 11, code 413",
                "The frontier Boolean is false at remaining fuel 10, original node 33207, the whole prefixCache at depth 11 and code 413, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4105-34986", "unmarked_context_12_4105_34986", "Unmarked parent at depth 12, code 4105",
                "The frontier Boolean is false at remaining fuel 9, original node 34986, the whole prefixCache at depth 12 and code 4105, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-413-33207", "node_context_11_413_33207", "Original split at fuel 10 and node 33207",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 33059, 33099, 33144, 33206. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4105-34986", "node_context_12_4105_34986", "Original split at fuel 9 and node 34986",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 34889, 34937, 34969, 34985. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-1652-33059", "context_12_1652_33059", "Context at depth 12, code 1652, node 33059",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1652 and original node 33059, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-16426-35093", "context_13_16426_35093", "Context at depth 13, code 16426, node 35093",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 16426 and original node 35093, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
