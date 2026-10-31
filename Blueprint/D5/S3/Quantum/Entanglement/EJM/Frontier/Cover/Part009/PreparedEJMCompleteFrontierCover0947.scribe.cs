using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0947Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0947.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0947",
        H("Original frontier context coverage 0947"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45460", "selected_cut_45460", "Selected cut at depth 12, code 367648, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 367648 returns the complete row with depth 12, base-four code 367648, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45507", "selected_cut_45507", "Selected cut at depth 13, code 1472565, node 1262955",
                "At remaining fuel 8 and original index 1262955, selection on the full partial prefix of depth 13 and code 1472565 returns the complete row with depth 13, base-four code 1472565, original node 1262955, kind 2, reserved field 0, 1017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-91911-1261199", "unmarked_context_11_91911_1261199", "Unmarked parent at depth 11, code 91911",
                "The frontier Boolean is false at remaining fuel 10, original node 1261199, the whole prefixCache at depth 11 and code 91911, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92034-1262898", "unmarked_context_11_92034_1262898", "Unmarked parent at depth 11, code 92034",
                "The frontier Boolean is false at remaining fuel 10, original node 1262898, the whole prefixCache at depth 11 and code 92034, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-91911-1261199", "node_context_11_91911_1261199", "Original split at fuel 10 and node 1261199",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1261016, 1261074, 1261147, 1261198. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92034-1262898", "node_context_11_92034_1262898", "Original split at fuel 10 and node 1262898",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1262809, 893903, 1262897. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-91911-1261199", "context_11_91911_1261199", "Context at depth 11, code 91911, node 1261199",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 91911 and original node 1261199, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_367644_1261016, context_12_367645_1261074, context_12_367646_1261147, context_12_367647_1261198.", DescribeRole.Theorem),
            Node("context-13-1472565-1262955", "context_13_1472565_1262955", "Context at depth 13, code 1472565, node 1262955",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1472565 and original node 1262955, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
