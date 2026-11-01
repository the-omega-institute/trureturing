using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1007Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1007.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1007",
        H("Original frontier context coverage 1007"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48340", "selected_cut_48340", "Selected cut at depth 11, code 93982, node 1356130",
                "At remaining fuel 10 and original index 1356130, selection on the full partial prefix of depth 11 and code 93982 returns the complete row with depth 11, base-four code 93982, original node 1356130, kind 2, reserved field 0, 2553 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48387", "selected_cut_48387", "Selected cut at depth 12, code 376101, node 891951",
                "At remaining fuel 9 and original index 891951, selection on the full partial prefix of depth 12 and code 376101 returns the complete row with depth 12, base-four code 376101, original node 891951, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23495-1356131", "unmarked_context_10_23495_1356131", "Unmarked parent at depth 10, code 23495",
                "The frontier Boolean is false at remaining fuel 11, original node 1356131, the whole prefixCache at depth 10 and code 23495, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-94024-1357591", "unmarked_context_11_94024_1357591", "Unmarked parent at depth 11, code 94024",
                "The frontier Boolean is false at remaining fuel 10, original node 1357591, the whole prefixCache at depth 11 and code 94024, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23495-1356131", "node_context_10_23495_1356131", "Original split at fuel 11 and node 1356131",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1356014, 1356081, 1356130, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-94024-1357591", "node_context_11_94024_1357591", "Original split at fuel 10 and node 1357591",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1357511, 1357550, 1357590. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93982-1356130", "context_11_93982_1356130", "Context at depth 11, code 93982, node 1356130",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93982 and original node 1356130, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-376101-891951", "context_12_376101_891951", "Context at depth 12, code 376101, node 891951",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 376101 and original node 891951, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
