using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0911Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0911.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0911",
        H("Original frontier context coverage 0911"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43731", "selected_cut_43731", "Selected cut at depth 12, code 352377, node 896706",
                "At remaining fuel 9 and original index 896706, selection on the full partial prefix of depth 12 and code 352377 returns the complete row with depth 12, base-four code 352377, original node 896706, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43778", "selected_cut_43778", "Selected cut at depth 12, code 352526, node 1200473",
                "At remaining fuel 9 and original index 1200473, selection on the full partial prefix of depth 12 and code 352526 returns the complete row with depth 12, base-four code 352526, original node 1200473, kind 2, reserved field 0, 2537 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88094-1199096", "unmarked_context_11_88094_1199096", "Unmarked parent at depth 11, code 88094",
                "The frontier Boolean is false at remaining fuel 10, original node 1199096, the whole prefixCache at depth 11 and code 88094, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88130-1200407", "unmarked_context_11_88130_1200407", "Unmarked parent at depth 11, code 88130",
                "The frontier Boolean is false at remaining fuel 10, original node 1200407, the whole prefixCache at depth 11 and code 88130, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88094-1199096", "node_context_11_88094_1199096", "Original split at fuel 10 and node 1199096",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1199042, 896706, 1199064, 1199095. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88130-1200407", "node_context_11_88130_1200407", "Original split at fuel 10 and node 1200407",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1200284, 1200344, 1200406. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-352377-896706", "context_12_352377_896706", "Context at depth 12, code 352377, node 896706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352377 and original node 896706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-352526-1200473", "context_12_352526_1200473", "Context at depth 12, code 352526, node 1200473",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352526 and original node 1200473, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
