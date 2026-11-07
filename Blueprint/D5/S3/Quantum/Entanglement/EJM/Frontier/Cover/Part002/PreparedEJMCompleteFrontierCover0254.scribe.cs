using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0254Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0254.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0254",
        H("Original frontier context coverage 0254"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12195", "selected_cut_12195", "Selected cut at depth 12, code 26028, node 323628",
                "At remaining fuel 9 and original index 323628, selection on the full partial prefix of depth 12 and code 26028 returns the complete row with depth 12, base-four code 26028, original node 323628, kind 2, reserved field 0, 1617 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12242", "selected_cut_12242", "Selected cut at depth 13, code 104462, node 324582",
                "At remaining fuel 8 and original index 324582, selection on the full partial prefix of depth 13 and code 104462 returns the complete row with depth 13, base-four code 104462, original node 324582, kind 2, reserved field 0, 2217 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6507-323682", "unmarked_context_11_6507_323682", "Unmarked parent at depth 11, code 6507",
                "The frontier Boolean is false at remaining fuel 10, original node 323682, the whole prefixCache at depth 11 and code 6507, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-104460-324470", "unmarked_context_13_104460_324470", "Unmarked parent at depth 13, code 104460",
                "The frontier Boolean is false at remaining fuel 8, original node 324470, the whole prefixCache at depth 13 and code 104460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6507-323682", "node_context_11_6507_323682", "Original split at fuel 10 and node 323682",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 323628, 323646, 323665, 323681. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-104460-324470", "node_context_13_104460_324470", "Original split at fuel 8 and node 324470",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 324430, 324445, 324454, 324469. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26028-323628", "context_12_26028_323628", "Context at depth 12, code 26028, node 323628",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26028 and original node 323628, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-104462-324582", "context_13_104462_324582", "Context at depth 13, code 104462, node 324582",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104462 and original node 324582, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
