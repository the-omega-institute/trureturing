using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0392Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0392.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0392",
        H("Original frontier context coverage 0392"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18819", "selected_cut_18819", "Selected cut at depth 14, code 1151091, node 481501",
                "At remaining fuel 7 and original index 481501, selection on the full partial prefix of depth 14 and code 1151091 returns the complete row with depth 14, base-four code 1151091, original node 481501, kind 2, reserved field 0, 1601 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18867", "selected_cut_18867", "Selected cut at depth 14, code 1151223, node 482897",
                "At remaining fuel 7 and original index 482897, selection on the full partial prefix of depth 14 and code 1151223 returns the complete row with depth 14, base-four code 1151223, original node 482897, kind 2, reserved field 0, 1097 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-287772-481502", "unmarked_context_13_287772_481502", "Unmarked parent at depth 13, code 287772",
                "The frontier Boolean is false at remaining fuel 8, original node 481502, the whole prefixCache at depth 13 and code 287772, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-287804-482834", "unmarked_context_13_287804_482834", "Unmarked parent at depth 13, code 287804",
                "The frontier Boolean is false at remaining fuel 8, original node 482834, the whole prefixCache at depth 13 and code 287804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-287772-481502", "node_context_13_287772_481502", "Original split at fuel 8 and node 481502",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 481407, 481437, 481469, 481501. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-287804-482834", "node_context_13_287804_482834", "Original split at fuel 8 and node 482834",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 482769, 482787, 482813, 482833. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-1151091-481501", "context_14_1151091_481501", "Context at depth 14, code 1151091, node 481501",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1151091 and original node 481501, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-1151223-482897", "context_14_1151223_482897", "Context at depth 14, code 1151223, node 482897",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1151223 and original node 482897, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
