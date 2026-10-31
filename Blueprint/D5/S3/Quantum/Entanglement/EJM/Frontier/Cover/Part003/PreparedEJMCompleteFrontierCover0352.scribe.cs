using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0352Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0352.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0352",
        H("Original frontier context coverage 0352"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16899", "selected_cut_16899", "Selected cut at depth 13, code 113937, node 429777",
                "At remaining fuel 8 and original index 429777, selection on the full partial prefix of depth 13 and code 113937 returns the complete row with depth 13, base-four code 113937, original node 429777, kind 2, reserved field 0, 3441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16946", "selected_cut_16946", "Selected cut at depth 13, code 113987, node 430773",
                "At remaining fuel 8 and original index 430773, selection on the full partial prefix of depth 13 and code 113987 returns the complete row with depth 13, base-four code 113987, original node 430773, kind 2, reserved field 0, 633 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28484-429815", "unmarked_context_12_28484_429815", "Unmarked parent at depth 12, code 28484",
                "The frontier Boolean is false at remaining fuel 9, original node 429815, the whole prefixCache at depth 12 and code 28484, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28496-430774", "unmarked_context_12_28496_430774", "Unmarked parent at depth 12, code 28496",
                "The frontier Boolean is false at remaining fuel 9, original node 430774, the whole prefixCache at depth 12 and code 28496, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28484-429815", "node_context_12_28484_429815", "Original split at fuel 9 and node 429815",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 429777, 429809, 429814. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28496-430774", "node_context_12_28496_430774", "Original split at fuel 9 and node 430774",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 430752, 430767, 430773. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-113937-429777", "context_13_113937_429777", "Context at depth 13, code 113937, node 429777",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113937 and original node 429777, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-28496-430774", "context_12_28496_430774", "Context at depth 12, code 28496, node 430774",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28496 and original node 430774, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_113984_3444, context_13_113985_430752, context_13_113986_430767, context_13_113987_430773.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
