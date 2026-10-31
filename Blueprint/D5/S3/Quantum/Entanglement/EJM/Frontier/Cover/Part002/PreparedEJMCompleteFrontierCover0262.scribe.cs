using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0262Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0262.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0262",
        H("Original frontier context coverage 0262"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12580", "selected_cut_12580", "Selected cut at depth 12, code 26212, node 331852",
                "At remaining fuel 9 and original index 331852, selection on the full partial prefix of depth 12 and code 26212 returns the complete row with depth 12, base-four code 26212, original node 331852, kind 2, reserved field 0, 3201 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12627", "selected_cut_12627", "Selected cut at depth 12, code 26238, node 333002",
                "At remaining fuel 9 and original index 333002, selection on the full partial prefix of depth 12 and code 26238 returns the complete row with depth 12, base-four code 26238, original node 333002, kind 2, reserved field 0, 2457 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26211-331811", "unmarked_context_12_26211_331811", "Unmarked parent at depth 12, code 26211",
                "The frontier Boolean is false at remaining fuel 9, original node 331811, the whole prefixCache at depth 12 and code 26211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26237-332970", "unmarked_context_12_26237_332970", "Unmarked parent at depth 12, code 26237",
                "The frontier Boolean is false at remaining fuel 9, original node 332970, the whole prefixCache at depth 12 and code 26237, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26211-331811", "node_context_12_26211_331811", "Original split at fuel 9 and node 331811",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 331781, 331805, 331810. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26237-332970", "node_context_12_26237_332970", "Original split at fuel 9 and node 332970",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 332905, 332951, 332969. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26211-331811", "context_12_26211_331811", "Context at depth 12, code 26211, node 331811",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26211 and original node 331811, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_104844_3444, context_13_104845_331781, context_13_104846_331805, context_13_104847_331810.", DescribeRole.Theorem),
            Node("context-12-26238-333002", "context_12_26238_333002", "Context at depth 12, code 26238, node 333002",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26238 and original node 333002, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
