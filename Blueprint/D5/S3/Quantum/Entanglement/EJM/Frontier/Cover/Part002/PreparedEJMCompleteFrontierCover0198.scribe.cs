using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0198Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0198.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0198",
        H("Original frontier context coverage 0198"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09507", "selected_cut_09507", "Selected cut at depth 13, code 93636, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 93636 returns the complete row with depth 13, base-four code 93636, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09554", "selected_cut_09554", "Selected cut at depth 12, code 23447, node 263849",
                "At remaining fuel 9 and original index 263849, selection on the full partial prefix of depth 12 and code 23447 returns the complete row with depth 12, base-four code 23447, original node 263849, kind 2, reserved field 0, 1897 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23409-262255", "unmarked_context_12_23409_262255", "Unmarked parent at depth 12, code 23409",
                "The frontier Boolean is false at remaining fuel 9, original node 262255, the whole prefixCache at depth 12 and code 23409, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5861-263850", "unmarked_context_11_5861_263850", "Unmarked parent at depth 11, code 5861",
                "The frontier Boolean is false at remaining fuel 10, original node 263850, the whole prefixCache at depth 11 and code 5861, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23409-262255", "node_context_12_23409_262255", "Original split at fuel 9 and node 262255",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 262183, 262230, 262254. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5861-263850", "node_context_11_5861_263850", "Original split at fuel 10 and node 263850",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 263775, 263797, 263827, 263849. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93636-3444", "context_13_93636_3444", "Context at depth 13, code 93636, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93636 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5861-263850", "context_11_5861_263850", "Context at depth 11, code 5861, node 263850",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5861 and original node 263850, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_23444_263775, context_12_23445_263797, context_12_23446_263827, context_12_23447_263849.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
