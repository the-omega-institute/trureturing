using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0489Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0489.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0489",
        H("Original frontier context coverage 0489"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23475", "selected_cut_23475", "Selected cut at depth 12, code 76428, node 594617",
                "At remaining fuel 9 and original index 594617, selection on the full partial prefix of depth 12 and code 76428 returns the complete row with depth 12, base-four code 76428, original node 594617, kind 2, reserved field 0, 1657 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23522", "selected_cut_23522", "Selected cut at depth 11, code 19121, node 595490",
                "At remaining fuel 10 and original index 595490, selection on the full partial prefix of depth 11 and code 19121 returns the complete row with depth 11, base-four code 19121, original node 595490, kind 2, reserved field 0, 3457 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19107-594693", "unmarked_context_11_19107_594693", "Unmarked parent at depth 11, code 19107",
                "The frontier Boolean is false at remaining fuel 10, original node 594693, the whole prefixCache at depth 11 and code 19107, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1194-595415", "unmarked_context_9_1194_595415", "Unmarked parent at depth 9, code 1194",
                "The frontier Boolean is false at remaining fuel 12, original node 595415, the whole prefixCache at depth 9 and code 1194, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19107-594693", "node_context_11_19107_594693", "Original split at fuel 10 and node 594693",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 594617, 594648, 594673, 594692. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1194-595415", "node_context_9_1194_595415", "Original split at fuel 12 and node 595415",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 594694, 595047, 595227, 595414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76428-594617", "context_12_76428_594617", "Context at depth 12, code 76428, node 594617",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76428 and original node 594617, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-19121-595490", "context_11_19121_595490", "Context at depth 11, code 19121, node 595490",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19121 and original node 595490, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
