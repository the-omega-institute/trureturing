using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0904Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0904.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0904",
        H("Original frontier context coverage 0904"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43394", "selected_cut_43394", "Selected cut at depth 12, code 349712, node 435160",
                "At remaining fuel 9 and original index 435160, selection on the full partial prefix of depth 12 and code 349712 returns the complete row with depth 12, base-four code 349712, original node 435160, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43442", "selected_cut_43442", "Selected cut at depth 11, code 87452, node 1188803",
                "At remaining fuel 10 and original index 1188803, selection on the full partial prefix of depth 11 and code 87452 returns the complete row with depth 11, base-four code 87452, original node 1188803, kind 2, reserved field 0, 2017 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-87428-1187372", "unmarked_context_11_87428_1187372", "Unmarked parent at depth 11, code 87428",
                "The frontier Boolean is false at remaining fuel 10, original node 1187372, the whole prefixCache at depth 11 and code 87428, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21862-1188749", "unmarked_context_10_21862_1188749", "Unmarked parent at depth 10, code 21862",
                "The frontier Boolean is false at remaining fuel 11, original node 1188749, the whole prefixCache at depth 10 and code 21862, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-87428-1187372", "node_context_11_87428_1187372", "Original split at fuel 10 and node 1187372",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1187273, 1187313, 1187371. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21862-1188749", "node_context_10_21862_1188749", "Original split at fuel 11 and node 1188749",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1188554, 1188621, 1188682, 1188748. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-349712-435160", "context_12_349712_435160", "Context at depth 12, code 349712, node 435160",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 349712 and original node 435160, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-87452-1188803", "context_11_87452_1188803", "Context at depth 11, code 87452, node 1188803",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 87452 and original node 1188803, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
