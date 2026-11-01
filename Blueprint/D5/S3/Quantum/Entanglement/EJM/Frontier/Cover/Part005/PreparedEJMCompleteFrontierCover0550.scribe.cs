using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0550Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0550.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0550",
        H("Original frontier context coverage 0550"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26404", "selected_cut_26404", "Selected cut at depth 13, code 355384, node 668011",
                "At remaining fuel 8 and original index 668011, selection on the full partial prefix of depth 13 and code 355384 returns the complete row with depth 13, base-four code 355384, original node 668011, kind 2, reserved field 0, 4093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26450", "selected_cut_26450", "Selected cut at depth 13, code 355424, node 669383",
                "At remaining fuel 8 and original index 669383, selection on the full partial prefix of depth 13 and code 355424 returns the complete row with depth 13, base-four code 355424, original node 669383, kind 2, reserved field 0, 1685 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88845-667936", "unmarked_context_12_88845_667936", "Unmarked parent at depth 12, code 88845",
                "The frontier Boolean is false at remaining fuel 9, original node 667936, the whole prefixCache at depth 12 and code 88845, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22213-669357", "unmarked_context_11_22213_669357", "Unmarked parent at depth 11, code 22213",
                "The frontier Boolean is false at remaining fuel 10, original node 669357, the whole prefixCache at depth 11 and code 22213, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88845-667936", "node_context_12_88845_667936", "Original split at fuel 9 and node 667936",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 667855, 667901, 667926, 667935. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22213-669357", "node_context_11_22213_669357", "Original split at fuel 10 and node 669357",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 669060, 669152, 669257, 669356. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-88845-667936", "context_12_88845_667936", "Context at depth 12, code 88845, node 667936",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88845 and original node 667936, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_355380_667855, context_13_355381_667901, context_13_355382_667926, context_13_355383_667935.", DescribeRole.Theorem),
            Node("context-13-355424-669383", "context_13_355424_669383", "Context at depth 13, code 355424, node 669383",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355424 and original node 669383, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
