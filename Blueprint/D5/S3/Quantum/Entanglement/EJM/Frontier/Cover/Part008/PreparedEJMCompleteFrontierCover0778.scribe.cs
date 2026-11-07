using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0778Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0778.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0778",
        H("Original frontier context coverage 0778"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37347", "selected_cut_37347", "Selected cut at depth 12, code 299640, node 998109",
                "At remaining fuel 9 and original index 998109, selection on the full partial prefix of depth 12 and code 299640 returns the complete row with depth 12, base-four code 299640, original node 998109, kind 2, reserved field 0, 1961 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37394", "selected_cut_37394", "Selected cut at depth 13, code 1199126, node 999356",
                "At remaining fuel 8 and original index 999356, selection on the full partial prefix of depth 13 and code 1199126 returns the complete row with depth 13, base-four code 1199126, original node 999356, kind 2, reserved field 0, 909 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74910-998180", "unmarked_context_11_74910_998180", "Unmarked parent at depth 11, code 74910",
                "The frontier Boolean is false at remaining fuel 10, original node 998180, the whole prefixCache at depth 11 and code 74910, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-299780-999284", "unmarked_context_12_299780_999284", "Unmarked parent at depth 12, code 299780",
                "The frontier Boolean is false at remaining fuel 9, original node 999284, the whole prefixCache at depth 12 and code 299780, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74910-998180", "node_context_11_74910_998180", "Original split at fuel 10 and node 998180",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 998109, 998145, 893903, 998179. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-299780-999284", "node_context_12_299780_999284", "Original split at fuel 9 and node 999284",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 999234, 999258, 999279, 999283. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-299640-998109", "context_12_299640_998109", "Context at depth 12, code 299640, node 998109",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299640 and original node 998109, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1199126-999356", "context_13_1199126_999356", "Context at depth 13, code 1199126, node 999356",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1199126 and original node 999356, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
