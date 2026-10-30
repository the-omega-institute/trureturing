using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0517Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0517.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0517",
        H("Original frontier context coverage 0517"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24820", "selected_cut_24820", "Selected cut at depth 13, code 309595, node 626698",
                "At remaining fuel 8 and original index 626698, selection on the full partial prefix of depth 13 and code 309595 returns the complete row with depth 13, base-four code 309595, original node 626698, kind 2, reserved field 0, 921 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24867", "selected_cut_24867", "Selected cut at depth 12, code 77427, node 628204",
                "At remaining fuel 9 and original index 628204, selection on the full partial prefix of depth 12 and code 77427 returns the complete row with depth 12, base-four code 77427, original node 628204, kind 2, reserved field 0, 3101 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77398-626699", "unmarked_context_12_77398_626699", "Unmarked parent at depth 12, code 77398",
                "The frontier Boolean is false at remaining fuel 9, original node 626699, the whole prefixCache at depth 12 and code 77398, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4838-628042", "unmarked_context_10_4838_628042", "Unmarked parent at depth 10, code 4838",
                "The frontier Boolean is false at remaining fuel 11, original node 628042, the whole prefixCache at depth 10 and code 4838, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77398-626699", "node_context_12_77398_626699", "Original split at fuel 9 and node 626699",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 626664, 626688, 626698. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4838-628042", "node_context_10_4838_628042", "Original split at fuel 11 and node 628042",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 627499, 627725, 627863, 628041. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-309595-626698", "context_13_309595_626698", "Context at depth 13, code 309595, node 626698",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 309595 and original node 626698, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77427-628204", "context_12_77427_628204", "Context at depth 12, code 77427, node 628204",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77427 and original node 628204, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
