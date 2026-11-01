using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0394Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0394.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0394",
        H("Original frontier context coverage 0394"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18915", "selected_cut_18915", "Selected cut at depth 13, code 287862, node 484605",
                "At remaining fuel 8 and original index 484605, selection on the full partial prefix of depth 13 and code 287862 returns the complete row with depth 13, base-four code 287862, original node 484605, kind 2, reserved field 0, 2137 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18962", "selected_cut_18962", "Selected cut at depth 13, code 287909, node 486107",
                "At remaining fuel 8 and original index 486107, selection on the full partial prefix of depth 13 and code 287909 returns the complete row with depth 13, base-four code 287909, original node 486107, kind 2, reserved field 0, 2905 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71965-484614", "unmarked_context_12_71965_484614", "Unmarked parent at depth 12, code 71965",
                "The frontier Boolean is false at remaining fuel 9, original node 484614, the whole prefixCache at depth 12 and code 71965, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71976-486043", "unmarked_context_12_71976_486043", "Unmarked parent at depth 12, code 71976",
                "The frontier Boolean is false at remaining fuel 9, original node 486043, the whole prefixCache at depth 12 and code 71976, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71965-484614", "node_context_12_71965_484614", "Original split at fuel 9 and node 484614",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 484547, 484582, 484605, 484613. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71976-486043", "node_context_12_71976_486043", "Original split at fuel 9 and node 486043",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 485794, 485937, 72292, 486042. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-287862-484605", "context_13_287862_484605", "Context at depth 13, code 287862, node 484605",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287862 and original node 484605, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-287909-486107", "context_13_287909_486107", "Context at depth 13, code 287909, node 486107",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287909 and original node 486107, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
