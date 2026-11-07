using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0400Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0400.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0400",
        H("Original frontier context coverage 0400"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19203", "selected_cut_19203", "Selected cut at depth 13, code 288162, node 490968",
                "At remaining fuel 8 and original index 490968, selection on the full partial prefix of depth 13 and code 288162 returns the complete row with depth 13, base-four code 288162, original node 490968, kind 2, reserved field 0, 2741 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19250", "selected_cut_19250", "Selected cut at depth 13, code 288224, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 288224 returns the complete row with depth 13, base-four code 288224, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72040-491006", "unmarked_context_12_72040_491006", "Unmarked parent at depth 12, code 72040",
                "The frontier Boolean is false at remaining fuel 9, original node 491006, the whole prefixCache at depth 12 and code 72040, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18013-491937", "unmarked_context_11_18013_491937", "Unmarked parent at depth 11, code 18013",
                "The frontier Boolean is false at remaining fuel 10, original node 491937, the whole prefixCache at depth 11 and code 18013, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72040-491006", "node_context_12_72040_491006", "Original split at fuel 9 and node 491006",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 490920, 490968, 491005. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18013-491937", "node_context_11_18013_491937", "Original split at fuel 10 and node 491937",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 491798, 441672, 491873, 491936. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-288162-490968", "context_13_288162_490968", "Context at depth 13, code 288162, node 490968",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288162 and original node 490968, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-288224-3444", "context_13_288224_3444", "Context at depth 13, code 288224, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288224 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
