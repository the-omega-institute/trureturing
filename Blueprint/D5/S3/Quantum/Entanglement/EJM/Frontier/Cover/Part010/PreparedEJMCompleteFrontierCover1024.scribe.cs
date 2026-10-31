using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1024Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1024.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1024",
        H("Original frontier context coverage 1024"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49155", "selected_cut_49155", "Selected cut at depth 10, code 25386, node 1388740",
                "At remaining fuel 11 and original index 1388740, selection on the full partial prefix of depth 10 and code 25386 returns the complete row with depth 10, base-four code 25386, original node 1388740, kind 2, reserved field 0, 973 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49202", "selected_cut_49202", "Selected cut at depth 11, code 101651, node 1390486",
                "At remaining fuel 10 and original index 1390486, selection on the full partial prefix of depth 11 and code 101651 returns the complete row with depth 11, base-four code 101651, original node 1390486, kind 2, reserved field 0, 2749 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6346-1388840", "unmarked_context_9_6346_1388840", "Unmarked parent at depth 9, code 6346",
                "The frontier Boolean is false at remaining fuel 12, original node 1388840, the whole prefixCache at depth 9 and code 6346, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6352-1390283", "unmarked_context_9_6352_1390283", "Unmarked parent at depth 9, code 6352",
                "The frontier Boolean is false at remaining fuel 12, original node 1390283, the whole prefixCache at depth 9 and code 6352, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6346-1388840", "node_context_9_6346_1388840", "Original split at fuel 12 and node 1388840",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1388601, 1388720, 1388740, 1388839. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6352-1390283", "node_context_9_6352_1390283", "Original split at fuel 12 and node 1390283",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1389149, 1389529, 1389949, 1390282. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-25386-1388740", "context_10_25386_1388740", "Context at depth 10, code 25386, node 1388740",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25386 and original node 1388740, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-101651-1390486", "context_11_101651_1390486", "Context at depth 11, code 101651, node 1390486",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101651 and original node 1390486, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
