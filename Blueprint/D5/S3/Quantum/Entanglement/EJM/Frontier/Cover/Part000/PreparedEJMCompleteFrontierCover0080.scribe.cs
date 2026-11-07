using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0080Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0080.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0080",
        H("Original frontier context coverage 0080"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03842", "selected_cut_03842", "Selected cut at depth 13, code 70667, node 123354",
                "At remaining fuel 8 and original index 123354, selection on the full partial prefix of depth 13 and code 70667 returns the complete row with depth 13, base-four code 70667, original node 123354, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03889", "selected_cut_03889", "Selected cut at depth 13, code 70759, node 124678",
                "At remaining fuel 8 and original index 124678, selection on the full partial prefix of depth 13 and code 70759 returns the complete row with depth 13, base-four code 70759, original node 124678, kind 2, reserved field 0, 789 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17666-123355", "unmarked_context_12_17666_123355", "Unmarked parent at depth 12, code 17666",
                "The frontier Boolean is false at remaining fuel 9, original node 123355, the whole prefixCache at depth 12 and code 17666, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-17689-124679", "unmarked_context_12_17689_124679", "Unmarked parent at depth 12, code 17689",
                "The frontier Boolean is false at remaining fuel 9, original node 124679, the whole prefixCache at depth 12 and code 17689, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17666-123355", "node_context_12_17666_123355", "Original split at fuel 9 and node 123355",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 123240, 123290, 123332, 123354. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-17689-124679", "node_context_12_17689_124679", "Original split at fuel 9 and node 124679",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 124626, 124647, 124667, 124678. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-70667-123354", "context_13_70667_123354", "Context at depth 13, code 70667, node 123354",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 70667 and original node 123354, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-17689-124679", "context_12_17689_124679", "Context at depth 12, code 17689, node 124679",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 17689 and original node 124679, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_70756_124626, context_13_70757_124647, context_13_70758_124667, context_13_70759_124678.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
