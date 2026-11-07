using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0289Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0289.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0289",
        H("Original frontier context coverage 0289"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13875", "selected_cut_13875", "Selected cut at depth 13, code 107748, node 362309",
                "At remaining fuel 8 and original index 362309, selection on the full partial prefix of depth 13 and code 107748 returns the complete row with depth 13, base-four code 107748, original node 362309, kind 2, reserved field 0, 373 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13922", "selected_cut_13922", "Selected cut at depth 13, code 107795, node 362988",
                "At remaining fuel 8 and original index 362988, selection on the full partial prefix of depth 13 and code 107795 returns the complete row with depth 13, base-four code 107795, original node 362988, kind 2, reserved field 0, 929 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26937-362356", "unmarked_context_12_26937_362356", "Unmarked parent at depth 12, code 26937",
                "The frontier Boolean is false at remaining fuel 9, original node 362356, the whole prefixCache at depth 12 and code 26937, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6736-362941", "unmarked_context_11_6736_362941", "Unmarked parent at depth 11, code 6736",
                "The frontier Boolean is false at remaining fuel 10, original node 362941, the whole prefixCache at depth 11 and code 6736, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26937-362356", "node_context_12_26937_362356", "Original split at fuel 9 and node 362356",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 362309, 362332, 362349, 362355. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6736-362941", "node_context_11_6736_362941", "Original split at fuel 10 and node 362941",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 362770, 362833, 362885, 362940. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-107748-362309", "context_13_107748_362309", "Context at depth 13, code 107748, node 362309",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107748 and original node 362309, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-107795-362988", "context_13_107795_362988", "Context at depth 13, code 107795, node 362988",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107795 and original node 362988, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
