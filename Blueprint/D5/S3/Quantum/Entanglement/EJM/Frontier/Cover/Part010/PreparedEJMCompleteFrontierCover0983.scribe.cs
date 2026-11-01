using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0983Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0983.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0983",
        H("Original frontier context coverage 0983"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47189", "selected_cut_47189", "Selected cut at depth 10, code 23285, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 23285 returns the complete row with depth 10, base-four code 23285, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47234", "selected_cut_47234", "Selected cut at depth 12, code 372764, node 1321536",
                "At remaining fuel 9 and original index 1321536, selection on the full partial prefix of depth 12 and code 372764 returns the complete row with depth 12, base-four code 372764, original node 1321536, kind 2, reserved field 0, 2405 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93139-1320235", "unmarked_context_11_93139_1320235", "Unmarked parent at depth 11, code 93139",
                "The frontier Boolean is false at remaining fuel 10, original node 1320235, the whole prefixCache at depth 11 and code 93139, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93190-1321497", "unmarked_context_11_93190_1321497", "Unmarked parent at depth 11, code 93190",
                "The frontier Boolean is false at remaining fuel 10, original node 1321497, the whole prefixCache at depth 11 and code 93190, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93139-1320235", "node_context_11_93139_1320235", "Original split at fuel 10 and node 1320235",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1320182, 1320214, 1320234, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93190-1321497", "node_context_11_93190_1321497", "Original split at fuel 10 and node 1321497",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1321457, 806997, 1321496. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93139-1320235", "context_11_93139_1320235", "Context at depth 11, code 93139, node 1320235",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93139 and original node 1320235, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_372556_1320182, context_12_372557_1320214, context_12_372558_1320234, context_12_372559_903806.", DescribeRole.Theorem),
            Node("context-12-372764-1321536", "context_12_372764_1321536", "Context at depth 12, code 372764, node 1321536",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 372764 and original node 1321536, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
