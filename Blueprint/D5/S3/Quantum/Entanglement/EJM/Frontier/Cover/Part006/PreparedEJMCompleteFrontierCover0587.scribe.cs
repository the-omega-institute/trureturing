using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0587Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0587.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0587",
        H("Original frontier context coverage 0587"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28179", "selected_cut_28179", "Selected cut at depth 13, code 368715, node 711463",
                "At remaining fuel 8 and original index 711463, selection on the full partial prefix of depth 13 and code 368715 returns the complete row with depth 13, base-four code 368715, original node 711463, kind 2, reserved field 0, 853 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28227", "selected_cut_28227", "Selected cut at depth 13, code 368763, node 712341",
                "At remaining fuel 8 and original index 712341, selection on the full partial prefix of depth 13 and code 368763 returns the complete row with depth 13, base-four code 368763, original node 712341, kind 2, reserved field 0, 861 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92178-711464", "unmarked_context_12_92178_711464", "Unmarked parent at depth 12, code 92178",
                "The frontier Boolean is false at remaining fuel 9, original node 711464, the whole prefixCache at depth 12 and code 92178, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92189-712277", "unmarked_context_12_92189_712277", "Unmarked parent at depth 12, code 92189",
                "The frontier Boolean is false at remaining fuel 9, original node 712277, the whole prefixCache at depth 12 and code 92189, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92178-711464", "node_context_12_92178_711464", "Original split at fuel 9 and node 711464",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 711420, 711443, 711456, 711463. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92189-712277", "node_context_12_92189_712277", "Original split at fuel 9 and node 712277",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 712226, 712253, 712271, 712276. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-368715-711463", "context_13_368715_711463", "Context at depth 13, code 368715, node 711463",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 368715 and original node 711463, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-368763-712341", "context_13_368763_712341", "Context at depth 13, code 368763, node 712341",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 368763 and original node 712341, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
