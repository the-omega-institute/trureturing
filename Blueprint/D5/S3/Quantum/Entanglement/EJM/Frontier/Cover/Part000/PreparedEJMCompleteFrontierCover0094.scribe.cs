using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0094Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0094.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0094",
        H("Original frontier context coverage 0094"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04515", "selected_cut_04515", "Selected cut at depth 12, code 18495, node 145420",
                "At remaining fuel 9 and original index 145420, selection on the full partial prefix of depth 12 and code 18495 returns the complete row with depth 12, base-four code 18495, original node 145420, kind 2, reserved field 0, 2989 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04561", "selected_cut_04561", "Selected cut at depth 13, code 74767, node 147485",
                "At remaining fuel 8 and original index 147485, selection on the full partial prefix of depth 13 and code 74767 returns the complete row with depth 13, base-four code 74767, original node 147485, kind 2, reserved field 0, 1117 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-4623-145421", "unmarked_context_11_4623_145421", "Unmarked parent at depth 11, code 4623",
                "The frontier Boolean is false at remaining fuel 10, original node 145421, the whole prefixCache at depth 11 and code 4623, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18691-147486", "unmarked_context_12_18691_147486", "Unmarked parent at depth 12, code 18691",
                "The frontier Boolean is false at remaining fuel 9, original node 147486, the whole prefixCache at depth 12 and code 18691, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-4623-145421", "node_context_11_4623_145421", "Original split at fuel 10 and node 145421",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 145206, 145274, 145361, 145420. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18691-147486", "node_context_12_18691_147486", "Original split at fuel 9 and node 147486",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 147383, 147439, 147474, 147485. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18495-145420", "context_12_18495_145420", "Context at depth 12, code 18495, node 145420",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18495 and original node 145420, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-18691-147486", "context_12_18691_147486", "Context at depth 12, code 18691, node 147486",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18691 and original node 147486, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_74764_147383, context_13_74765_147439, context_13_74766_147474, context_13_74767_147485.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
