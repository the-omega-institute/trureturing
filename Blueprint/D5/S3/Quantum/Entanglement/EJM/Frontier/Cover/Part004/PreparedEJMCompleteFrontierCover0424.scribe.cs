using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0424Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0424.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0424",
        H("Original frontier context coverage 0424"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20354", "selected_cut_20354", "Selected cut at depth 12, code 73829, node 522481",
                "At remaining fuel 9 and original index 522481, selection on the full partial prefix of depth 12 and code 73829 returns the complete row with depth 12, base-four code 73829, original node 522481, kind 2, reserved field 0, 2393 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20402", "selected_cut_20402", "Selected cut at depth 13, code 295982, node 524422",
                "At remaining fuel 8 and original index 524422, selection on the full partial prefix of depth 13 and code 295982 returns the complete row with depth 13, base-four code 295982, original node 524422, kind 2, reserved field 0, 2213 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18457-522607", "unmarked_context_11_18457_522607", "Unmarked parent at depth 11, code 18457",
                "The frontier Boolean is false at remaining fuel 10, original node 522607, the whole prefixCache at depth 11 and code 18457, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-73993-524301", "unmarked_context_12_73993_524301", "Unmarked parent at depth 12, code 73993",
                "The frontier Boolean is false at remaining fuel 9, original node 524301, the whole prefixCache at depth 12 and code 73993, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18457-522607", "node_context_11_18457_522607", "Original split at fuel 10 and node 522607",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 4595, 522481, 522549, 522606. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-73993-524301", "node_context_12_73993_524301", "Original split at fuel 9 and node 524301",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 524211, 524248, 524286, 524300. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-73829-522481", "context_12_73829_522481", "Context at depth 12, code 73829, node 522481",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 73829 and original node 522481, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-295982-524422", "context_13_295982_524422", "Context at depth 13, code 295982, node 524422",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 295982 and original node 524422, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
