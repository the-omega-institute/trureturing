using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0800Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0800.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0800",
        H("Original frontier context coverage 0800"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38403", "selected_cut_38403", "Selected cut at depth 12, code 301383, node 1035120",
                "At remaining fuel 9 and original index 1035120, selection on the full partial prefix of depth 12 and code 301383 returns the complete row with depth 12, base-four code 301383, original node 1035120, kind 2, reserved field 0, 2285 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38450", "selected_cut_38450", "Selected cut at depth 11, code 75368, node 1036632",
                "At remaining fuel 10 and original index 1036632, selection on the full partial prefix of depth 11 and code 75368 returns the complete row with depth 11, base-four code 75368, original node 1036632, kind 2, reserved field 0, 2229 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75345-1035121", "unmarked_context_11_75345_1035121", "Unmarked parent at depth 11, code 75345",
                "The frontier Boolean is false at remaining fuel 10, original node 1035121, the whole prefixCache at depth 11 and code 75345, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18841-1036596", "unmarked_context_10_18841_1036596", "Unmarked parent at depth 10, code 18841",
                "The frontier Boolean is false at remaining fuel 11, original node 1036596, the whole prefixCache at depth 10 and code 18841, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75345-1035121", "node_context_11_75345_1035121", "Original split at fuel 10 and node 1035121",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1035030, 891951, 1035077, 1035120. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18841-1036596", "node_context_10_18841_1036596", "Original split at fuel 11 and node 1036596",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1036481, 1036516, 1036554, 1036595. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301383-1035120", "context_12_301383_1035120", "Context at depth 12, code 301383, node 1035120",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301383 and original node 1035120, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-75368-1036632", "context_11_75368_1036632", "Context at depth 11, code 75368, node 1036632",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75368 and original node 1036632, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
