using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0261Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0261.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0261",
        H("Original frontier context coverage 0261"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12531", "selected_cut_12531", "Selected cut at depth 12, code 26190, node 330738",
                "At remaining fuel 9 and original index 330738, selection on the full partial prefix of depth 12 and code 26190 returns the complete row with depth 12, base-four code 26190, original node 330738, kind 2, reserved field 0, 3997 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12579", "selected_cut_12579", "Selected cut at depth 13, code 104847, node 331810",
                "At remaining fuel 8 and original index 331810, selection on the full partial prefix of depth 13 and code 104847 returns the complete row with depth 13, base-four code 104847, original node 331810, kind 2, reserved field 0, 961 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26191-330801", "unmarked_context_12_26191_330801", "Unmarked parent at depth 12, code 26191",
                "The frontier Boolean is false at remaining fuel 9, original node 330801, the whole prefixCache at depth 12 and code 26191, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26209-331715", "unmarked_context_12_26209_331715", "Unmarked parent at depth 12, code 26209",
                "The frontier Boolean is false at remaining fuel 9, original node 331715, the whole prefixCache at depth 12 and code 26209, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26191-330801", "node_context_12_26191_330801", "Original split at fuel 9 and node 330801",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 330772, 330792, 330800. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26209-331715", "node_context_12_26209_331715", "Original split at fuel 9 and node 331715",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 331649, 331697, 331714. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26190-330738", "context_12_26190_330738", "Context at depth 12, code 26190, node 330738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26190 and original node 330738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-104847-331810", "context_13_104847_331810", "Context at depth 13, code 104847, node 331810",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104847 and original node 331810, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
