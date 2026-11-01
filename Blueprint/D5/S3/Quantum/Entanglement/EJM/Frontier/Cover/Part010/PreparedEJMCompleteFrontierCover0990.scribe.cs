using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0990Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0990.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0990",
        H("Original frontier context coverage 0990"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47524", "selected_cut_47524", "Selected cut at depth 12, code 373552, node 792260",
                "At remaining fuel 9 and original index 792260, selection on the full partial prefix of depth 12 and code 373552 returns the complete row with depth 12, base-four code 373552, original node 792260, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47571", "selected_cut_47571", "Selected cut at depth 11, code 93414, node 1331811",
                "At remaining fuel 10 and original index 1331811, selection on the full partial prefix of depth 11 and code 93414 returns the complete row with depth 11, base-four code 93414, original node 1331811, kind 2, reserved field 0, 2125 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23346-1330321", "unmarked_context_10_23346_1330321", "Unmarked parent at depth 10, code 23346",
                "The frontier Boolean is false at remaining fuel 11, original node 1330321, the whole prefixCache at depth 10 and code 23346, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23352-1331704", "unmarked_context_10_23352_1331704", "Unmarked parent at depth 10, code 23352",
                "The frontier Boolean is false at remaining fuel 11, original node 1331704, the whole prefixCache at depth 10 and code 23352, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23346-1330321", "node_context_10_23346_1330321", "Original split at fuel 11 and node 1330321",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1329950, 1330119, 1330155, 1330320. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23352-1331704", "node_context_10_23352_1331704", "Original split at fuel 11 and node 1331704",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1331620, 1331671, 1331703. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23346-1330321", "context_10_23346_1330321", "Context at depth 10, code 23346, node 1330321",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23346 and original node 1330321, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93384_1329950, context_11_93385_1330119, context_11_93386_1330155, context_11_93387_1330320.", DescribeRole.Theorem),
            Node("context-11-93414-1331811", "context_11_93414_1331811", "Context at depth 11, code 93414, node 1331811",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93414 and original node 1331811, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
