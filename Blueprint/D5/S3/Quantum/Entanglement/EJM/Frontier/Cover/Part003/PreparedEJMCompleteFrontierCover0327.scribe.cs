using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0327Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0327.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0327",
        H("Original frontier context coverage 0327"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15699", "selected_cut_15699", "Selected cut at depth 13, code 111699, node 402278",
                "At remaining fuel 8 and original index 402278, selection on the full partial prefix of depth 13 and code 111699 returns the complete row with depth 13, base-four code 111699, original node 402278, kind 2, reserved field 0, 653 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15746", "selected_cut_15746", "Selected cut at depth 13, code 111749, node 403247",
                "At remaining fuel 8 and original index 403247, selection on the full partial prefix of depth 13 and code 111749 returns the complete row with depth 13, base-four code 111749, original node 403247, kind 2, reserved field 0, 2341 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27924-402279", "unmarked_context_12_27924_402279", "Unmarked parent at depth 12, code 27924",
                "The frontier Boolean is false at remaining fuel 9, original node 402279, the whole prefixCache at depth 12 and code 27924, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27936-403212", "unmarked_context_12_27936_403212", "Unmarked parent at depth 12, code 27936",
                "The frontier Boolean is false at remaining fuel 9, original node 403212, the whole prefixCache at depth 12 and code 27936, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27924-402279", "node_context_12_27924_402279", "Original split at fuel 9 and node 402279",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 402226, 402251, 402270, 402278. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27936-403212", "node_context_12_27936_403212", "Original split at fuel 9 and node 403212",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 403158, 403180, 403203, 403211. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111699-402278", "context_13_111699_402278", "Context at depth 13, code 111699, node 402278",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111699 and original node 402278, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111749-403247", "context_13_111749_403247", "Context at depth 13, code 111749, node 403247",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111749 and original node 403247, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
