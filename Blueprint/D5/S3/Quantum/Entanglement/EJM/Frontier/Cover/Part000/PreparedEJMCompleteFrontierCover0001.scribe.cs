using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0001Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0001.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0001",
        H("Original frontier context coverage 0001"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00049", "selected_cut_00049", "Selected cut at depth 13, code 1027, node 414",
                "At remaining fuel 8 and original index 414, selection on the full partial prefix of depth 13 and code 1027 returns the complete row with depth 13, base-four code 1027, original node 414, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00097", "selected_cut_00097", "Selected cut at depth 13, code 1069, node 6889",
                "At remaining fuel 8 and original index 6889, selection on the full partial prefix of depth 13 and code 1069 returns the complete row with depth 13, base-four code 1069, original node 6889, kind 2, reserved field 0, 2673 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-256-4967", "unmarked_context_12_256_4967", "Unmarked parent at depth 12, code 256",
                "The frontier Boolean is false at remaining fuel 9, original node 4967, the whole prefixCache at depth 12 and code 256, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-1068-6786", "unmarked_context_13_1068_6786", "Unmarked parent at depth 13, code 1068",
                "The frontier Boolean is false at remaining fuel 8, original node 6786, the whole prefixCache at depth 13 and code 1068, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-256-4967", "node_context_12_256_4967", "Original split at fuel 9 and node 4967",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 4780, 4891, 4966, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-1068-6786", "node_context_13_1068_6786", "Original split at fuel 8 and node 6786",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 6667, 6708, 6749, 6785. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1027-414", "context_13_1027_414", "Context at depth 13, code 1027, node 414",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1027 and original node 414, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1069-6889", "context_13_1069_6889", "Context at depth 13, code 1069, node 6889",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1069 and original node 6889, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
