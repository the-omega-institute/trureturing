using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0393Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0393.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0393",
        H("Original frontier context coverage 0393"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18868", "selected_cut_18868", "Selected cut at depth 13, code 287806, node 482984",
                "At remaining fuel 8 and original index 482984, selection on the full partial prefix of depth 13 and code 287806 returns the complete row with depth 13, base-four code 287806, original node 482984, kind 2, reserved field 0, 3345 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18914", "selected_cut_18914", "Selected cut at depth 13, code 287861, node 484582",
                "At remaining fuel 8 and original index 484582, selection on the full partial prefix of depth 13 and code 287861 returns the complete row with depth 13, base-four code 287861, original node 484582, kind 2, reserved field 0, 2321 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-287805-482898", "unmarked_context_13_287805_482898", "Unmarked parent at depth 13, code 287805",
                "The frontier Boolean is false at remaining fuel 8, original node 482898, the whole prefixCache at depth 13 and code 287805, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71964-484508", "unmarked_context_12_71964_484508", "Unmarked parent at depth 12, code 71964",
                "The frontier Boolean is false at remaining fuel 9, original node 484508, the whole prefixCache at depth 12 and code 71964, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-287805-482898", "node_context_13_287805_482898", "Original split at fuel 8 and node 482898",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 482843, 482857, 482878, 482897. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71964-484508", "node_context_12_71964_484508", "Original split at fuel 9 and node 484508",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 484358, 484413, 484472, 484507. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-287805-482898", "context_13_287805_482898", "Context at depth 13, code 287805, node 482898",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287805 and original node 482898, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_1151220_482843, context_14_1151221_482857, context_14_1151222_482878, context_14_1151223_482897.", DescribeRole.Theorem),
            Node("context-13-287861-484582", "context_13_287861_484582", "Context at depth 13, code 287861, node 484582",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287861 and original node 484582, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
