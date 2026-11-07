using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0300Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0300.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0300",
        H("Original frontier context coverage 0300"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14404", "selected_cut_14404", "Selected cut at depth 13, code 108796, node 372175",
                "At remaining fuel 8 and original index 372175, selection on the full partial prefix of depth 13 and code 108796 returns the complete row with depth 13, base-four code 108796, original node 372175, kind 2, reserved field 0, 81 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14451", "selected_cut_14451", "Selected cut at depth 13, code 108846, node 373064",
                "At remaining fuel 8 and original index 373064, selection on the full partial prefix of depth 13 and code 108846 returns the complete row with depth 13, base-four code 108846, original node 373064, kind 2, reserved field 0, 1197 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27199-372221", "unmarked_context_12_27199_372221", "Unmarked parent at depth 12, code 27199",
                "The frontier Boolean is false at remaining fuel 9, original node 372221, the whole prefixCache at depth 12 and code 27199, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27210-373019", "unmarked_context_12_27210_373019", "Unmarked parent at depth 12, code 27210",
                "The frontier Boolean is false at remaining fuel 9, original node 373019, the whole prefixCache at depth 12 and code 27210, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27199-372221", "node_context_12_27199_372221", "Original split at fuel 9 and node 372221",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 372175, 372201, 372215, 372220. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27210-373019", "node_context_12_27210_373019", "Original split at fuel 9 and node 373019",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 372970, 373005, 373018. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-108796-372175", "context_13_108796_372175", "Context at depth 13, code 108796, node 372175",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108796 and original node 372175, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-108846-373064", "context_13_108846_373064", "Context at depth 13, code 108846, node 373064",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108846 and original node 373064, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
