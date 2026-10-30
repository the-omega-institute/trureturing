using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0174Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0174.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0174",
        H("Original frontier context coverage 0174"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08355", "selected_cut_08355", "Selected cut at depth 12, code 22920, node 234343",
                "At remaining fuel 9 and original index 234343, selection on the full partial prefix of depth 12 and code 22920 returns the complete row with depth 12, base-four code 22920, original node 234343, kind 2, reserved field 0, 2413 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08402", "selected_cut_08402", "Selected cut at depth 12, code 22967, node 235236",
                "At remaining fuel 9 and original index 235236, selection on the full partial prefix of depth 12 and code 22967 returns the complete row with depth 12, base-four code 22967, original node 235236, kind 2, reserved field 0, 1121 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5729-234316", "unmarked_context_11_5729_234316", "Unmarked parent at depth 11, code 5729",
                "The frontier Boolean is false at remaining fuel 10, original node 234316, the whole prefixCache at depth 11 and code 5729, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5741-235237", "unmarked_context_11_5741_235237", "Unmarked parent at depth 11, code 5741",
                "The frontier Boolean is false at remaining fuel 10, original node 235237, the whole prefixCache at depth 11 and code 5741, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5729-234316", "node_context_11_5729_234316", "Original split at fuel 10 and node 234316",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 234234, 234263, 234288, 234315. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5741-235237", "node_context_11_5741_235237", "Original split at fuel 10 and node 235237",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 235198, 235213, 235224, 235236. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5729-234316", "context_11_5729_234316", "Context at depth 11, code 5729, node 234316",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5729 and original node 234316, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22916_234234, context_12_22917_234263, context_12_22918_234288, context_12_22919_234315.", DescribeRole.Theorem),
            Node("context-11-5741-235237", "context_11_5741_235237", "Context at depth 11, code 5741, node 235237",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5741 and original node 235237, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22964_235198, context_12_22965_235213, context_12_22966_235224, context_12_22967_235236.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
