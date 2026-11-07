using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0771Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0771.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0771",
        H("Original frontier context coverage 0771"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37011", "selected_cut_37011", "Selected cut at depth 12, code 299127, node 988006",
                "At remaining fuel 9 and original index 988006, selection on the full partial prefix of depth 12 and code 299127 returns the complete row with depth 12, base-four code 299127, original node 988006, kind 2, reserved field 0, 1661 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37057", "selected_cut_37057", "Selected cut at depth 12, code 299269, node 891951",
                "At remaining fuel 9 and original index 891951, selection on the full partial prefix of depth 12 and code 299269 returns the complete row with depth 12, base-four code 299269, original node 891951, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74781-988007", "unmarked_context_11_74781_988007", "Unmarked parent at depth 11, code 74781",
                "The frontier Boolean is false at remaining fuel 10, original node 988007, the whole prefixCache at depth 11 and code 74781, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-299268-989139", "unmarked_context_12_299268_989139", "Unmarked parent at depth 12, code 299268",
                "The frontier Boolean is false at remaining fuel 9, original node 989139, the whole prefixCache at depth 12 and code 299268, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74781-988007", "node_context_11_74781_988007", "Original split at fuel 10 and node 988007",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 987931, 987958, 987980, 988006. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-299268-989139", "node_context_12_299268_989139", "Original split at fuel 9 and node 989139",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 989078, 989110, 989131, 989138. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-299127-988006", "context_12_299127_988006", "Context at depth 12, code 299127, node 988006",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299127 and original node 988006, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-299269-891951", "context_12_299269_891951", "Context at depth 12, code 299269, node 891951",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299269 and original node 891951, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
