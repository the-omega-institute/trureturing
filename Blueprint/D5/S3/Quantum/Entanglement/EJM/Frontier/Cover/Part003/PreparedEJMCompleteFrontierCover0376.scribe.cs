using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0376Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0376.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0376",
        H("Original frontier context coverage 0376"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18050", "selected_cut_18050", "Selected cut at depth 12, code 71189, node 449506",
                "At remaining fuel 9 and original index 449506, selection on the full partial prefix of depth 12 and code 71189 returns the complete row with depth 12, base-four code 71189, original node 449506, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18098", "selected_cut_18098", "Selected cut at depth 13, code 284810, node 464232",
                "At remaining fuel 8 and original index 464232, selection on the full partial prefix of depth 13 and code 284810 returns the complete row with depth 13, base-four code 284810, original node 464232, kind 2, reserved field 0, 1229 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71190-463271", "unmarked_context_12_71190_463271", "Unmarked parent at depth 12, code 71190",
                "The frontier Boolean is false at remaining fuel 9, original node 463271, the whole prefixCache at depth 12 and code 71190, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71201-464171", "unmarked_context_12_71201_464171", "Unmarked parent at depth 12, code 71201",
                "The frontier Boolean is false at remaining fuel 9, original node 464171, the whole prefixCache at depth 12 and code 71201, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71190-463271", "node_context_12_71190_463271", "Original split at fuel 9 and node 463271",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 463212, 463238, 463259, 463270. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71201-464171", "node_context_12_71201_464171", "Original split at fuel 9 and node 464171",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 464115, 464145, 464165, 464170. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71189-449506", "context_12_71189_449506", "Context at depth 12, code 71189, node 449506",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71189 and original node 449506, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-284810-464232", "context_13_284810_464232", "Context at depth 13, code 284810, node 464232",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 284810 and original node 464232, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
