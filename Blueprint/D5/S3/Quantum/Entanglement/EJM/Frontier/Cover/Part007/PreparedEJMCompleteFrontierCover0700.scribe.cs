using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0700Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0700.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0700",
        H("Original frontier context coverage 0700"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33604", "selected_cut_33604", "Selected cut at depth 13, code 441520, node 865397",
                "At remaining fuel 8 and original index 865397, selection on the full partial prefix of depth 13 and code 441520 returns the complete row with depth 13, base-four code 441520, original node 865397, kind 2, reserved field 0, 721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33652", "selected_cut_33652", "Selected cut at depth 13, code 441571, node 866279",
                "At remaining fuel 8 and original index 866279, selection on the full partial prefix of depth 13 and code 441571 returns the complete row with depth 13, base-four code 441571, original node 866279, kind 2, reserved field 0, 661 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110380-865458", "unmarked_context_12_110380_865458", "Unmarked parent at depth 12, code 110380",
                "The frontier Boolean is false at remaining fuel 9, original node 865458, the whole prefixCache at depth 12 and code 110380, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27597-866173", "unmarked_context_11_27597_866173", "Unmarked parent at depth 11, code 27597",
                "The frontier Boolean is false at remaining fuel 10, original node 866173, the whole prefixCache at depth 11 and code 27597, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110380-865458", "node_context_12_110380_865458", "Original split at fuel 9 and node 865458",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 865397, 865432, 865453, 865457. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27597-866173", "node_context_11_27597_866173", "Original split at fuel 10 and node 866173",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 865980, 866041, 866102, 866172. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-441520-865397", "context_13_441520_865397", "Context at depth 13, code 441520, node 865397",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 441520 and original node 865397, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-441571-866279", "context_13_441571_866279", "Context at depth 13, code 441571, node 866279",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 441571 and original node 866279, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
