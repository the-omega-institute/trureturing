using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0425Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0425.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0425",
        H("Original frontier context coverage 0425"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20403", "selected_cut_20403", "Selected cut at depth 13, code 295983, node 524430",
                "At remaining fuel 8 and original index 524430, selection on the full partial prefix of depth 13 and code 295983 returns the complete row with depth 13, base-four code 295983, original node 524430, kind 2, reserved field 0, 985 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20450", "selected_cut_20450", "Selected cut at depth 13, code 296045, node 525301",
                "At remaining fuel 8 and original index 525301, selection on the full partial prefix of depth 13 and code 296045 returns the complete row with depth 13, base-four code 296045, original node 525301, kind 2, reserved field 0, 2153 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-73995-524431", "unmarked_context_12_73995_524431", "Unmarked parent at depth 12, code 73995",
                "The frontier Boolean is false at remaining fuel 9, original node 524431, the whole prefixCache at depth 12 and code 73995, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-74010-525252", "unmarked_context_12_74010_525252", "Unmarked parent at depth 12, code 74010",
                "The frontier Boolean is false at remaining fuel 9, original node 525252, the whole prefixCache at depth 12 and code 74010, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-73995-524431", "node_context_12_73995_524431", "Original split at fuel 9 and node 524431",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 524364, 524395, 524422, 524430. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-74010-525252", "node_context_12_74010_525252", "Original split at fuel 9 and node 525252",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 525206, 525229, 525245, 525251. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-295983-524430", "context_13_295983_524430", "Context at depth 13, code 295983, node 524430",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 295983 and original node 524430, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-296045-525301", "context_13_296045_525301", "Context at depth 13, code 296045, node 525301",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 296045 and original node 525301, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
