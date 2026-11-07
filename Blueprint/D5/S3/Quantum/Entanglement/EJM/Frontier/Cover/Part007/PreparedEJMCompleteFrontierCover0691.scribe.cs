using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0691Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0691.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0691",
        H("Original frontier context coverage 0691"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33172", "selected_cut_33172", "Selected cut at depth 13, code 440410, node 854825",
                "At remaining fuel 8 and original index 854825, selection on the full partial prefix of depth 13 and code 440410 returns the complete row with depth 13, base-four code 440410, original node 854825, kind 2, reserved field 0, 1241 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33219", "selected_cut_33219", "Selected cut at depth 13, code 440460, node 855856",
                "At remaining fuel 8 and original index 855856, selection on the full partial prefix of depth 13 and code 440460 returns the complete row with depth 13, base-four code 440460, original node 855856, kind 2, reserved field 0, 1217 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110102-854835", "unmarked_context_12_110102_854835", "Unmarked parent at depth 12, code 110102",
                "The frontier Boolean is false at remaining fuel 9, original node 854835, the whole prefixCache at depth 12 and code 110102, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-110114-855840", "unmarked_context_12_110114_855840", "Unmarked parent at depth 12, code 110114",
                "The frontier Boolean is false at remaining fuel 9, original node 855840, the whole prefixCache at depth 12 and code 110114, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110102-854835", "node_context_12_110102_854835", "Original split at fuel 9 and node 854835",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 854780, 854806, 854825, 854834. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-110114-855840", "node_context_12_110114_855840", "Original split at fuel 9 and node 855840",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 855792, 855815, 855830, 855839. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-440410-854825", "context_13_440410_854825", "Context at depth 13, code 440410, node 854825",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 440410 and original node 854825, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-440460-855856", "context_13_440460_855856", "Context at depth 13, code 440460, node 855856",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 440460 and original node 855856, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
