using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0614Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0614.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0614",
        H("Original frontier context coverage 0614"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29476", "selected_cut_29476", "Selected cut at depth 12, code 93547, node 743941",
                "At remaining fuel 9 and original index 743941, selection on the full partial prefix of depth 12 and code 93547 returns the complete row with depth 12, base-four code 93547, original node 743941, kind 2, reserved field 0, 3273 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29523", "selected_cut_29523", "Selected cut at depth 12, code 93594, node 745226",
                "At remaining fuel 9 and original index 745226, selection on the full partial prefix of depth 12 and code 93594 returns the complete row with depth 12, base-four code 93594, original node 745226, kind 2, reserved field 0, 1841 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23386-743942", "unmarked_context_11_23386_743942", "Unmarked parent at depth 11, code 23386",
                "The frontier Boolean is false at remaining fuel 10, original node 743942, the whole prefixCache at depth 11 and code 23386, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23397-745152", "unmarked_context_11_23397_745152", "Unmarked parent at depth 11, code 23397",
                "The frontier Boolean is false at remaining fuel 10, original node 745152, the whole prefixCache at depth 11 and code 23397, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23386-743942", "node_context_11_23386_743942", "Original split at fuel 10 and node 743942",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 743849, 691709, 743897, 743941. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23397-745152", "node_context_11_23397_745152", "Original split at fuel 10 and node 745152",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 745108, 439069, 745130, 745151. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93547-743941", "context_12_93547_743941", "Context at depth 12, code 93547, node 743941",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93547 and original node 743941, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93594-745226", "context_12_93594_745226", "Context at depth 12, code 93594, node 745226",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93594 and original node 745226, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
