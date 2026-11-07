using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0813Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0813.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0813",
        H("Original frontier context coverage 0813"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39028", "selected_cut_39028", "Selected cut at depth 12, code 302440, node 1057616",
                "At remaining fuel 9 and original index 1057616, selection on the full partial prefix of depth 12 and code 302440 returns the complete row with depth 12, base-four code 302440, original node 1057616, kind 2, reserved field 0, 2097 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39075", "selected_cut_39075", "Selected cut at depth 11, code 75639, node 1058819",
                "At remaining fuel 10 and original index 1058819, selection on the full partial prefix of depth 11 and code 75639 returns the complete row with depth 11, base-four code 75639, original node 1058819, kind 2, reserved field 0, 937 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75609-1057586", "unmarked_context_11_75609_1057586", "Unmarked parent at depth 11, code 75609",
                "The frontier Boolean is false at remaining fuel 10, original node 1057586, the whole prefixCache at depth 11 and code 75609, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18908-1058739", "unmarked_context_10_18908_1058739", "Unmarked parent at depth 10, code 18908",
                "The frontier Boolean is false at remaining fuel 11, original node 1058739, the whole prefixCache at depth 10 and code 18908, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75609-1057586", "node_context_11_75609_1057586", "Original split at fuel 10 and node 1057586",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1057530, 891951, 1057556, 1057585. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18908-1058739", "node_context_10_18908_1058739", "Original split at fuel 11 and node 1058739",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1058634, 1058666, 1058697, 1058738. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-75609-1057586", "context_11_75609_1057586", "Context at depth 11, code 75609, node 1057586",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75609 and original node 1057586, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_302436_1057530, context_12_302437_891951, context_12_302438_1057556, context_12_302439_1057585.", DescribeRole.Theorem),
            Node("context-11-75639-1058819", "context_11_75639_1058819", "Context at depth 11, code 75639, node 1058819",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75639 and original node 1058819, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
