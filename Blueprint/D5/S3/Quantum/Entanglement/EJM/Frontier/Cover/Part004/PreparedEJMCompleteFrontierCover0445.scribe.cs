using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0445Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0445.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0445",
        H("Original frontier context coverage 0445"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21362", "selected_cut_21362", "Selected cut at depth 13, code 300101, node 546760",
                "At remaining fuel 8 and original index 546760, selection on the full partial prefix of depth 13 and code 300101 returns the complete row with depth 13, base-four code 300101, original node 546760, kind 2, reserved field 0, 1729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21410", "selected_cut_21410", "Selected cut at depth 13, code 300155, node 548079",
                "At remaining fuel 8 and original index 548079, selection on the full partial prefix of depth 13 and code 300155 returns the complete row with depth 13, base-four code 300155, original node 548079, kind 2, reserved field 0, 941 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75025-546786", "unmarked_context_12_75025_546786", "Unmarked parent at depth 12, code 75025",
                "The frontier Boolean is false at remaining fuel 9, original node 546786, the whole prefixCache at depth 12 and code 75025, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75038-548080", "unmarked_context_12_75038_548080", "Unmarked parent at depth 12, code 75038",
                "The frontier Boolean is false at remaining fuel 9, original node 548080, the whole prefixCache at depth 12 and code 75038, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75025-546786", "node_context_12_75025_546786", "Original split at fuel 9 and node 546786",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 546737, 546760, 546778, 546785. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75038-548080", "node_context_12_75038_548080", "Original split at fuel 9 and node 548080",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 548025, 548050, 548073, 548079. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-300101-546760", "context_13_300101_546760", "Context at depth 13, code 300101, node 546760",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300101 and original node 546760, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75038-548080", "context_12_75038_548080", "Context at depth 12, code 75038, node 548080",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75038 and original node 548080, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_300152_548025, context_13_300153_548050, context_13_300154_548073, context_13_300155_548079.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
