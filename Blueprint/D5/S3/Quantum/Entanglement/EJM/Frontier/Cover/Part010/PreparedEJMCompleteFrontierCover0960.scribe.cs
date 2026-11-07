using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0960Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0960.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0960",
        H("Original frontier context coverage 0960"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46082", "selected_cut_46082", "Selected cut at depth 11, code 92432, node 1283168",
                "At remaining fuel 10 and original index 1283168, selection on the full partial prefix of depth 11 and code 92432 returns the complete row with depth 11, base-four code 92432, original node 1283168, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46129", "selected_cut_46129", "Selected cut at depth 10, code 23119, node 1284680",
                "At remaining fuel 11 and original index 1284680, selection on the full partial prefix of depth 10 and code 23119 returns the complete row with depth 10, base-four code 23119, original node 1284680, kind 2, reserved field 0, 209 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92433-1283312", "unmarked_context_11_92433_1283312", "Unmarked parent at depth 11, code 92433",
                "The frontier Boolean is false at remaining fuel 10, original node 1283312, the whole prefixCache at depth 11 and code 92433, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1444-1284682", "unmarked_context_8_1444_1284682", "Unmarked parent at depth 8, code 1444",
                "The frontier Boolean is false at remaining fuel 13, original node 1284682, the whole prefixCache at depth 8 and code 1444, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92433-1283312", "node_context_11_92433_1283312", "Original split at fuel 10 and node 1283312",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1283218, 692443, 1283263, 1283311. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1444-1284682", "node_context_8_1444_1284682", "Original split at fuel 13 and node 1284682",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1283167, 1284140, 1284496, 1284681. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92432-1283168", "context_11_92432_1283168", "Context at depth 11, code 92432, node 1283168",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92432 and original node 1283168, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-8-1444-1284682", "context_8_1444_1284682", "Context at depth 8, code 1444, node 1284682",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 1444 and original node 1284682, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_5776_1283167, context_9_5777_1284140, context_9_5778_1284496, context_9_5779_1284681.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
