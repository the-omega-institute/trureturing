using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0605Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0605.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0605",
        H("Original frontier context coverage 0605"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29044", "selected_cut_29044", "Selected cut at depth 13, code 372952, node 733300",
                "At remaining fuel 8 and original index 733300, selection on the full partial prefix of depth 13 and code 372952 returns the complete row with depth 13, base-four code 372952, original node 733300, kind 2, reserved field 0, 389 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29090", "selected_cut_29090", "Selected cut at depth 12, code 93269, node 642341",
                "At remaining fuel 9 and original index 642341, selection on the full partial prefix of depth 12 and code 93269 returns the complete row with depth 12, base-four code 93269, original node 642341, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93237-733294", "unmarked_context_12_93237_733294", "Unmarked parent at depth 12, code 93237",
                "The frontier Boolean is false at remaining fuel 9, original node 733294, the whole prefixCache at depth 12 and code 93237, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23316-734437", "unmarked_context_11_23316_734437", "Unmarked parent at depth 11, code 23316",
                "The frontier Boolean is false at remaining fuel 10, original node 734437, the whole prefixCache at depth 11 and code 23316, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93237-733294", "node_context_12_93237_733294", "Original split at fuel 9 and node 733294",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 733236, 733260, 733287, 733293. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23316-734437", "node_context_11_23316_734437", "Original split at fuel 10 and node 734437",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 266170, 642341, 734386, 734436. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93237-733294", "context_12_93237_733294", "Context at depth 12, code 93237, node 733294",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93237 and original node 733294, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_372948_733236, context_13_372949_733260, context_13_372950_733287, context_13_372951_733293.", DescribeRole.Theorem),
            Node("context-12-93269-642341", "context_12_93269_642341", "Context at depth 12, code 93269, node 642341",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93269 and original node 642341, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
