using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0838Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0838.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0838",
        H("Original frontier context coverage 0838"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40228", "selected_cut_40228", "Selected cut at depth 12, code 308845, node 1092950",
                "At remaining fuel 9 and original index 1092950, selection on the full partial prefix of depth 12 and code 308845 returns the complete row with depth 12, base-four code 308845, original node 1092950, kind 2, reserved field 0, 1545 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40275", "selected_cut_40275", "Selected cut at depth 13, code 1236024, node 1094224",
                "At remaining fuel 8 and original index 1094224, selection on the full partial prefix of depth 13 and code 1236024 returns the complete row with depth 13, base-four code 1236024, original node 1094224, kind 2, reserved field 0, 1285 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77211-1093012", "unmarked_context_11_77211_1093012", "Unmarked parent at depth 11, code 77211",
                "The frontier Boolean is false at remaining fuel 10, original node 1093012, the whole prefixCache at depth 11 and code 77211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-309004-1094136", "unmarked_context_12_309004_1094136", "Unmarked parent at depth 12, code 309004",
                "The frontier Boolean is false at remaining fuel 9, original node 1094136, the whole prefixCache at depth 12 and code 309004, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77211-1093012", "node_context_11_77211_1093012", "Original split at fuel 10 and node 1093012",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1092920, 1092950, 1092980, 1093011. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-309004-1094136", "node_context_12_309004_1094136", "Original split at fuel 9 and node 1094136",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1094054, 1094094, 1094121, 1094135. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-308845-1092950", "context_12_308845_1092950", "Context at depth 12, code 308845, node 1092950",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308845 and original node 1092950, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1236024-1094224", "context_13_1236024_1094224", "Context at depth 13, code 1236024, node 1094224",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1236024 and original node 1094224, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
