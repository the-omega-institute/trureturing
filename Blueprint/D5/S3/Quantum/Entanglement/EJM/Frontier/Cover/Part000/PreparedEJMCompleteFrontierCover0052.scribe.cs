using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0052Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0052.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0052",
        H("Original frontier context coverage 0052"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02498", "selected_cut_02498", "Selected cut at depth 13, code 22817, node 80072",
                "At remaining fuel 8 and original index 80072, selection on the full partial prefix of depth 13 and code 22817 returns the complete row with depth 13, base-four code 22817, original node 80072, kind 2, reserved field 0, 2349 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02546", "selected_cut_02546", "Selected cut at depth 13, code 22862, node 80892",
                "At remaining fuel 8 and original index 80892, selection on the full partial prefix of depth 13 and code 22862 returns the complete row with depth 13, base-four code 22862, original node 80892, kind 2, reserved field 0, 2161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5704-80106", "unmarked_context_12_5704_80106", "Unmarked parent at depth 12, code 5704",
                "The frontier Boolean is false at remaining fuel 9, original node 80106, the whole prefixCache at depth 12 and code 5704, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5714-80840", "unmarked_context_12_5714_80840", "Unmarked parent at depth 12, code 5714",
                "The frontier Boolean is false at remaining fuel 9, original node 80840, the whole prefixCache at depth 12 and code 5714, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5704-80106", "node_context_12_5704_80106", "Original split at fuel 9 and node 80106",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 80072, 80094, 80105. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5714-80840", "node_context_12_5714_80840", "Original split at fuel 9 and node 80840",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 80805, 80824, 80839. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-22817-80072", "context_13_22817_80072", "Context at depth 13, code 22817, node 80072",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22817 and original node 80072, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-22862-80892", "context_13_22862_80892", "Context at depth 13, code 22862, node 80892",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22862 and original node 80892, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
