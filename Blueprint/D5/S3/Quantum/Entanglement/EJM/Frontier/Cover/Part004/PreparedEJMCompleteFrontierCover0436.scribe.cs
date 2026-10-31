using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0436Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0436.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0436",
        H("Original frontier context coverage 0436"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20931", "selected_cut_20931", "Selected cut at depth 12, code 74610, node 536672",
                "At remaining fuel 9 and original index 536672, selection on the full partial prefix of depth 12 and code 74610 returns the complete row with depth 12, base-four code 74610, original node 536672, kind 2, reserved field 0, 2073 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20977", "selected_cut_20977", "Selected cut at depth 12, code 74764, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 74764 returns the complete row with depth 12, base-four code 74764, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18652-536697", "unmarked_context_11_18652_536697", "Unmarked parent at depth 11, code 18652",
                "The frontier Boolean is false at remaining fuel 10, original node 536697, the whole prefixCache at depth 11 and code 18652, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18690-538295", "unmarked_context_11_18690_538295", "Unmarked parent at depth 11, code 18690",
                "The frontier Boolean is false at remaining fuel 10, original node 538295, the whole prefixCache at depth 11 and code 18690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18652-536697", "node_context_11_18652_536697", "Original split at fuel 10 and node 536697",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 536607, 536637, 536672, 536696. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18690-538295", "node_context_11_18690_538295", "Original split at fuel 10 and node 538295",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 538129, 524302, 538294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-74610-536672", "context_12_74610_536672", "Context at depth 12, code 74610, node 536672",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74610 and original node 536672, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-74764-448748", "context_12_74764_448748", "Context at depth 12, code 74764, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74764 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
