using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0518Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0518.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0518",
        H("Original frontier context coverage 0518"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24868", "selected_cut_24868", "Selected cut at depth 12, code 77428, node 628241",
                "At remaining fuel 9 and original index 628241, selection on the full partial prefix of depth 12 and code 77428 returns the complete row with depth 12, base-four code 77428, original node 628241, kind 2, reserved field 0, 2653 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24914", "selected_cut_24914", "Selected cut at depth 12, code 77471, node 629631",
                "At remaining fuel 9 and original index 629631, selection on the full partial prefix of depth 12 and code 77471 returns the complete row with depth 12, base-four code 77471, original node 629631, kind 2, reserved field 0, 2289 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19356-628205", "unmarked_context_11_19356_628205", "Unmarked parent at depth 11, code 19356",
                "The frontier Boolean is false at remaining fuel 10, original node 628205, the whole prefixCache at depth 11 and code 19356, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4841-629633", "unmarked_context_10_4841_629633", "Unmarked parent at depth 10, code 4841",
                "The frontier Boolean is false at remaining fuel 11, original node 629633, the whole prefixCache at depth 10 and code 4841, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19356-628205", "node_context_11_19356_628205", "Original split at fuel 10 and node 628205",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 628086, 628123, 628164, 628204. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4841-629633", "node_context_10_4841_629633", "Original split at fuel 11 and node 629633",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 629280, 629408, 629510, 629632. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19356-628205", "context_11_19356_628205", "Context at depth 11, code 19356, node 628205",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19356 and original node 628205, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77424_628086, context_12_77425_628123, context_12_77426_628164, context_12_77427_628204.", DescribeRole.Theorem),
            Node("context-10-4841-629633", "context_10_4841_629633", "Context at depth 10, code 4841, node 629633",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4841 and original node 629633, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_19364_629280, context_11_19365_629408, context_11_19366_629510, context_11_19367_629632.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
