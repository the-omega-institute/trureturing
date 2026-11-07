using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0361Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0361.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0361",
        H("Original frontier context coverage 0361"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17331", "selected_cut_17331", "Selected cut at depth 13, code 279735, node 440870",
                "At remaining fuel 8 and original index 440870, selection on the full partial prefix of depth 13 and code 279735 returns the complete row with depth 13, base-four code 279735, original node 440870, kind 2, reserved field 0, 893 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17377", "selected_cut_17377", "Selected cut at depth 10, code 4375, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 4375 returns the complete row with depth 10, base-four code 4375, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-69933-440871", "unmarked_context_12_69933_440871", "Unmarked parent at depth 12, code 69933",
                "The frontier Boolean is false at remaining fuel 9, original node 440871, the whole prefixCache at depth 12 and code 69933, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4374-442240", "unmarked_context_10_4374_442240", "Unmarked parent at depth 10, code 4374",
                "The frontier Boolean is false at remaining fuel 11, original node 442240, the whole prefixCache at depth 10 and code 4374, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-69933-440871", "node_context_12_69933_440871", "Original split at fuel 9 and node 440871",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 440813, 440836, 440864, 440870. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4374-442240", "node_context_10_4374_442240", "Original split at fuel 11 and node 442240",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 441627, 441790, 442042, 442239. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-279735-440870", "context_13_279735_440870", "Context at depth 13, code 279735, node 440870",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 279735 and original node 440870, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-4375-3440", "context_10_4375_3440", "Context at depth 10, code 4375, node 3440",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4375 and original node 3440, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
