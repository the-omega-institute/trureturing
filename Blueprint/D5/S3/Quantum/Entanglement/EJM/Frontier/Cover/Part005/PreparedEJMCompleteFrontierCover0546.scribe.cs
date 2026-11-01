using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0546Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0546.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0546",
        H("Original frontier context coverage 0546"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26212", "selected_cut_26212", "Selected cut at depth 13, code 354553, node 662920",
                "At remaining fuel 8 and original index 662920, selection on the full partial prefix of depth 13 and code 354553 returns the complete row with depth 13, base-four code 354553, original node 662920, kind 2, reserved field 0, 2553 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26258", "selected_cut_26258", "Selected cut at depth 12, code 88661, node 642341",
                "At remaining fuel 9 and original index 642341, selection on the full partial prefix of depth 12 and code 88661 returns the complete row with depth 12, base-four code 88661, original node 642341, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88638-662959", "unmarked_context_12_88638_662959", "Unmarked parent at depth 12, code 88638",
                "The frontier Boolean is false at remaining fuel 9, original node 662959, the whole prefixCache at depth 12 and code 88638, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22164-664014", "unmarked_context_11_22164_664014", "Unmarked parent at depth 11, code 22164",
                "The frontier Boolean is false at remaining fuel 10, original node 664014, the whole prefixCache at depth 11 and code 22164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88638-662959", "node_context_12_88638_662959", "Original split at fuel 9 and node 662959",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 662880, 662920, 662952, 662958. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22164-664014", "node_context_11_22164_664014", "Original split at fuel 10 and node 664014",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 663912, 642341, 663957, 664013. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-354553-662920", "context_13_354553_662920", "Context at depth 13, code 354553, node 662920",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354553 and original node 662920, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-88661-642341", "context_12_88661_642341", "Context at depth 12, code 88661, node 642341",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88661 and original node 642341, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
