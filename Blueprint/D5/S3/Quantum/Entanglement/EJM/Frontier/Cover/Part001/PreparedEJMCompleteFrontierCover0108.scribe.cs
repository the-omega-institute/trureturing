using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0108Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0108.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0108",
        H("Original frontier context coverage 0108"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05187", "selected_cut_05187", "Selected cut at depth 13, code 76905, node 161118",
                "At remaining fuel 8 and original index 161118, selection on the full partial prefix of depth 13 and code 76905 returns the complete row with depth 13, base-four code 76905, original node 161118, kind 2, reserved field 0, 2861 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05234", "selected_cut_05234", "Selected cut at depth 13, code 76952, node 162361",
                "At remaining fuel 8 and original index 162361, selection on the full partial prefix of depth 13 and code 76952 returns the complete row with depth 13, base-four code 76952, original node 162361, kind 2, reserved field 0, 1401 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-19226-161146", "unmarked_context_12_19226_161146", "Unmarked parent at depth 12, code 19226",
                "The frontier Boolean is false at remaining fuel 9, original node 161146, the whole prefixCache at depth 12 and code 19226, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-19237-162337", "unmarked_context_12_19237_162337", "Unmarked parent at depth 12, code 19237",
                "The frontier Boolean is false at remaining fuel 9, original node 162337, the whole prefixCache at depth 12 and code 19237, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-19226-161146", "node_context_12_19226_161146", "Original split at fuel 9 and node 161146",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 161087, 161118, 161139, 161145. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-19237-162337", "node_context_12_19237_162337", "Original split at fuel 9 and node 162337",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 162265, 162310, 162327, 162336. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-76905-161118", "context_13_76905_161118", "Context at depth 13, code 76905, node 161118",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 76905 and original node 161118, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-76952-162361", "context_13_76952_162361", "Context at depth 13, code 76952, node 162361",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 76952 and original node 162361, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
