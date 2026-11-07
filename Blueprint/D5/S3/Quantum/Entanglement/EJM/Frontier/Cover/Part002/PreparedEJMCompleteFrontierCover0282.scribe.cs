using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0282Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0282.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0282",
        H("Original frontier context coverage 0282"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13540", "selected_cut_13540", "Selected cut at depth 13, code 106927, node 354798",
                "At remaining fuel 8 and original index 354798, selection on the full partial prefix of depth 13 and code 106927 returns the complete row with depth 13, base-four code 106927, original node 354798, kind 2, reserved field 0, 1297 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13585", "selected_cut_13585", "Selected cut at depth 12, code 26767, node 356001",
                "At remaining fuel 9 and original index 356001, selection on the full partial prefix of depth 12 and code 26767 returns the complete row with depth 12, base-four code 26767, original node 356001, kind 2, reserved field 0, 1881 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26731-354799", "unmarked_context_12_26731_354799", "Unmarked parent at depth 12, code 26731",
                "The frontier Boolean is false at remaining fuel 9, original node 354799, the whole prefixCache at depth 12 and code 26731, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1672-356003", "unmarked_context_10_1672_356003", "Unmarked parent at depth 10, code 1672",
                "The frontier Boolean is false at remaining fuel 11, original node 356003, the whole prefixCache at depth 10 and code 1672, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26731-354799", "node_context_12_26731_354799", "Original split at fuel 9 and node 354799",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 354763, 354784, 354798. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1672-356003", "node_context_10_1672_356003", "Original split at fuel 11 and node 356003",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 355686, 355797, 355904, 356002. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106927-354798", "context_13_106927_354798", "Context at depth 13, code 106927, node 354798",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106927 and original node 354798, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1672-356003", "context_10_1672_356003", "Context at depth 10, code 1672, node 356003",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1672 and original node 356003, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6688_355686, context_11_6689_355797, context_11_6690_355904, context_11_6691_356002.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
