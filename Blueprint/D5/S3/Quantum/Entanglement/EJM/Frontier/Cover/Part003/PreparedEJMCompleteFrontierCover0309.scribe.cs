using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0309Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0309.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0309",
        H("Original frontier context coverage 0309"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14836", "selected_cut_14836", "Selected cut at depth 13, code 109774, node 382265",
                "At remaining fuel 8 and original index 382265, selection on the full partial prefix of depth 13 and code 109774 returns the complete row with depth 13, base-four code 109774, original node 382265, kind 2, reserved field 0, 1513 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14884", "selected_cut_14884", "Selected cut at depth 13, code 109822, node 382997",
                "At remaining fuel 8 and original index 382997, selection on the full partial prefix of depth 13 and code 109822 returns the complete row with depth 13, base-four code 109822, original node 382997, kind 2, reserved field 0, 2085 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27443-382272", "unmarked_context_12_27443_382272", "Unmarked parent at depth 12, code 27443",
                "The frontier Boolean is false at remaining fuel 9, original node 382272, the whole prefixCache at depth 12 and code 27443, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27454-382896", "unmarked_context_12_27454_382896", "Unmarked parent at depth 12, code 27454",
                "The frontier Boolean is false at remaining fuel 9, original node 382896, the whole prefixCache at depth 12 and code 27454, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27443-382272", "node_context_12_27443_382272", "Original split at fuel 9 and node 382272",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 382220, 382246, 382265, 382271. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27454-382896", "node_context_12_27454_382896", "Original split at fuel 9 and node 382896",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 382849, 382874, 382891, 382895. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109774-382265", "context_13_109774_382265", "Context at depth 13, code 109774, node 382265",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109774 and original node 382265, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-109822-382997", "context_13_109822_382997", "Context at depth 13, code 109822, node 382997",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109822 and original node 382997, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
