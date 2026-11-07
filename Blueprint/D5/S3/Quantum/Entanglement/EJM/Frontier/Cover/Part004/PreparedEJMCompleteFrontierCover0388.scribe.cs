using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0388Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0388.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0388",
        H("Original frontier context coverage 0388"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18627", "selected_cut_18627", "Selected cut at depth 13, code 287055, node 476704",
                "At remaining fuel 8 and original index 476704, selection on the full partial prefix of depth 13 and code 287055 returns the complete row with depth 13, base-four code 287055, original node 476704, kind 2, reserved field 0, 789 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18673", "selected_cut_18673", "Selected cut at depth 13, code 287104, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 287104 returns the complete row with depth 13, base-four code 287104, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71763-476705", "unmarked_context_12_71763_476705", "Unmarked parent at depth 12, code 71763",
                "The frontier Boolean is false at remaining fuel 9, original node 476705, the whole prefixCache at depth 12 and code 71763, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4485-477376", "unmarked_context_10_4485_477376", "Unmarked parent at depth 10, code 4485",
                "The frontier Boolean is false at remaining fuel 11, original node 477376, the whole prefixCache at depth 10 and code 4485, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71763-476705", "node_context_12_71763_476705", "Original split at fuel 9 and node 476705",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 476682, 476698, 476704. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4485-477376", "node_context_10_4485_477376", "Original split at fuel 11 and node 477376",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 476706, 476971, 477191, 477375. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-287055-476704", "context_13_287055_476704", "Context at depth 13, code 287055, node 476704",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287055 and original node 476704, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-287104-3444", "context_13_287104_3444", "Context at depth 13, code 287104, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287104 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
