using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0085Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0085.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0085",
        H("Original frontier context coverage 0085"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04082", "selected_cut_04082", "Selected cut at depth 13, code 71777, node 129992",
                "At remaining fuel 8 and original index 129992, selection on the full partial prefix of depth 13 and code 71777 returns the complete row with depth 13, base-four code 71777, original node 129992, kind 2, reserved field 0, 1601 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04129", "selected_cut_04129", "Selected cut at depth 13, code 71824, node 131035",
                "At remaining fuel 8 and original index 131035, selection on the full partial prefix of depth 13 and code 71824 returns the complete row with depth 13, base-four code 71824, original node 131035, kind 2, reserved field 0, 1045 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17944-130019", "unmarked_context_12_17944_130019", "Unmarked parent at depth 12, code 17944",
                "The frontier Boolean is false at remaining fuel 9, original node 130019, the whole prefixCache at depth 12 and code 17944, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4488-131015", "unmarked_context_11_4488_131015", "Unmarked parent at depth 11, code 4488",
                "The frontier Boolean is false at remaining fuel 10, original node 131015, the whole prefixCache at depth 11 and code 4488, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17944-130019", "node_context_12_17944_130019", "Original split at fuel 9 and node 130019",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 129970, 129992, 130011, 130018. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4488-131015", "node_context_11_4488_131015", "Original split at fuel 10 and node 131015",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 130746, 130839, 130913, 131014. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-71777-129992", "context_13_71777_129992", "Context at depth 13, code 71777, node 129992",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 71777 and original node 129992, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-71824-131035", "context_13_71824_131035", "Context at depth 13, code 71824, node 131035",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 71824 and original node 131035, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
