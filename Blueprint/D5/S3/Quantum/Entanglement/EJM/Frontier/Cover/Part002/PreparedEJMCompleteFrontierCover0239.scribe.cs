using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0239Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0239.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0239",
        H("Original frontier context coverage 0239"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11475", "selected_cut_11475", "Selected cut at depth 13, code 102636, node 307016",
                "At remaining fuel 8 and original index 307016, selection on the full partial prefix of depth 13 and code 102636 returns the complete row with depth 13, base-four code 102636, original node 307016, kind 2, reserved field 0, 257 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11521", "selected_cut_11521", "Selected cut at depth 13, code 102691, node 307915",
                "At remaining fuel 8 and original index 307915, selection on the full partial prefix of depth 13 and code 102691 returns the complete row with depth 13, base-four code 102691, original node 307915, kind 2, reserved field 0, 1001 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25659-307113", "unmarked_context_12_25659_307113", "Unmarked parent at depth 12, code 25659",
                "The frontier Boolean is false at remaining fuel 9, original node 307113, the whole prefixCache at depth 12 and code 25659, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25672-307916", "unmarked_context_12_25672_307916", "Unmarked parent at depth 12, code 25672",
                "The frontier Boolean is false at remaining fuel 9, original node 307916, the whole prefixCache at depth 12 and code 25672, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25659-307113", "node_context_12_25659_307113", "Original split at fuel 9 and node 307113",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 307016, 307082, 307105, 307112. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25672-307916", "node_context_12_25672_307916", "Original split at fuel 9 and node 307916",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 307876, 307900, 307915. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-102636-307016", "context_13_102636_307016", "Context at depth 13, code 102636, node 307016",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102636 and original node 307016, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25672-307916", "context_12_25672_307916", "Context at depth 12, code 25672, node 307916",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25672 and original node 307916, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_102688_3444, context_13_102689_307876, context_13_102690_307900, context_13_102691_307915.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
